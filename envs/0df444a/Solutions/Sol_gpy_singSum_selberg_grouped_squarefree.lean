-- Prove2me | solution 1 for gpy_singSum_selberg_grouped_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T19:25:33.809993+00:00
-- url     : https://prove2.me/submissions/e0aa478c-fd80-4259-b6ee-98de51f8acae

/-
  Submission file for the Prove2Me problem `gpy_singSum_selberg_grouped_squarefree`
  (publish2 batch, conditional monomial evaluation).

  Self-contained: imports Mathlib only. Contains the verified
  bodies needed for the theorem (support, good pairs, Selberg
  weight, singular sum, monomial pair sums, modulus grouping,
  squarefree vanishing, fiber bound, Abel summation), the
  original theorem, the restated theorem, and top-level
  `theorem solution` in the problem's exact binder/statement
  form (statement mechanically extracted from the restated
  theorem, so the two are textually identical). No sorry
  tactic, no axioms beyond the standard ones, no platform
  imports. The conditional theorem is published AS a
  conditional theorem (hMono as an explicit hypothesis).
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace GPY

def tupleSupport (k : ℕ) (R : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)

/-- Membership in the support set, unfolded. -/

theorem mem_tupleSupport {k : ℕ} {R : ℕ} {d : Fin k → ℕ} :
    d ∈ tupleSupport k R ↔
      (∀ i, 1 ≤ d i) ∧ (∀ i, d i ≤ R) ∧ ∏ i, d i ≤ R := by
  rw [tupleSupport, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (Finset.mem_Icc.mp (h1 i)).1,
      fun i => (Finset.mem_Icc.mp (h1 i)).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, h2 i⟩, h3⟩

/-- The GPY weight at n for the tuple h, level R, and coefficients λ:
    the square of the divisor sum over the support. -/

def goodPair {k : ℕ} (h d e : Fin k → ℕ) (i : Fin k) : Prop :=
  ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))

/-- The summed model error over ALL residues mod `L` at height `Y`.
    Summing over all residues (not just coprime ones) keeps the statement
    witness-free and needs no coprimality transport; it costs at most a
    factor `L` against the max-residue form BV bounds, which the future
    error-control lemma will work with directly. -/

noncomputable def lamSelberg (k : ℕ) (R : ℕ) (deg : ℕ) (d : Fin k → ℕ) : ℝ :=
  if ∏ i, d i ≤ R then
    (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
      * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
  else 0

/-- On the support, the weight is the μ-times-polynomial form. -/

theorem lamSelberg_eq_of_mem_support {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) :
    lamSelberg k R deg d
      = (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg := by
  unfold lamSelberg
  rw [if_pos (mem_tupleSupport.mp hd).2.2]

/-- The weight vanishes off squarefree products: Möbius kills them. -/

def tupleProdCount (k : ℕ) (D : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun d => ∏ i, d i = D)).card

/-- The fiber of the support over a product `D ≤ R` has card
    `τ_k(D)`: a support tuple with product `D` has all entries at
    most `D` (each entry is at most the product, since the other
    factors are at least 1), and conversely entries at most `D` with
    product `D` are automatically at most `R` and in the support. -/

noncomputable def singSum (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) : ℝ := by
  classical
  exact ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if goodPair h d e i then lam d * lam e
      / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
    else 0

/-- Triple-sum commutation, used to move the coordinate sum outside
    the pair sums. -/

theorem sum_sum_sum_comm {α γ : Type*} {s : Finset α} {u : Finset γ}
    (F : α → α → γ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, ∑ i ∈ u, F d e i)
      = ∑ i ∈ u, ∑ d ∈ s, ∑ e ∈ s, F d e i := by
  calc (∑ d ∈ s, ∑ e ∈ s, ∑ i ∈ u, F d e i)
      = ∑ p ∈ s ×ˢ s, ∑ i ∈ u, F p.1 p.2 i :=
        (Finset.sum_product' (s := s) (t := s)
          (f := fun d e => ∑ i ∈ u, F d e i)).symm
    _ = ∑ i ∈ u, ∑ p ∈ s ×ˢ s, F p.1 p.2 i := Finset.sum_comm
    _ = ∑ i ∈ u, ∑ d ∈ s, ∑ e ∈ s, F d e i := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_product' (s := s) (t := s) (f := fun d e => F d e i)

/-- The BV main term for the model `li/φ` factors as a sum over
    coordinates of the li-difference times the singular-series sum:
    the li-differences do not depend on `(d, e)`, so they factor out
    of the pair sums, leaving a pure λ-sum. -/

theorem lcm_le_sq_of_mem_support {k : ℕ} {R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) (he : e ∈ tupleSupport k R) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≤ R ^ 2 := by
  classical
  have hd1 : ∀ j, 1 ≤ d j := (mem_tupleSupport.mp hd).1
  have hdprod : ∏ j, d j ≤ R := (mem_tupleSupport.mp hd).2.2
  have he1 : ∀ j, 1 ≤ e j := (mem_tupleSupport.mp he).1
  have heprod : ∏ j, e j ≤ R := (mem_tupleSupport.mp he).2.2
  have hmne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 := by
    intro j
    apply Nat.lcm_ne_zero
    · have h1 := hd1 j
      omega
    · have h2 := he1 j
      omega
  have hprodpos : 0 < ∏ j, Nat.lcm (d j) (e j) :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => hmne j))
  have hdvd : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ∣ ∏ j, Nat.lcm (d j) (e j) :=
    Finset.lcm_dvd (fun j _ => Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  have hle1 : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ≤ ∏ j, Nat.lcm (d j) (e j) :=
    Nat.le_of_dvd hprodpos hdvd
  have hle2 : ∏ j, Nat.lcm (d j) (e j) ≤ ∏ j, (d j * e j) := by
    apply Finset.prod_le_prod'
    intro j _
    have h1 : GCDMonoid.lcm (d j) (e j) ∣ d j * e j :=
      lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _)
    rw [lcm_eq_nat_lcm] at h1
    exact Nat.le_of_dvd (mul_pos (by have h := hd1 j; omega) (by have h := he1 j; omega)) h1
  have hle3 : ∏ j, (d j * e j) = (∏ j, d j) * (∏ j, e j) := Finset.prod_mul_distrib
  have hle4 : (∏ j, d j) * (∏ j, e j) ≤ R * R := Nat.mul_le_mul hdprod heprod
  calc Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      ≤ ∏ j, Nat.lcm (d j) (e j) := hle1
    _ ≤ ∏ j, (d j * e j) := hle2
    _ = (∏ j, d j) * (∏ j, e j) := hle3
    _ ≤ R * R := hle4
    _ = R ^ 2 := (pow_two R).symm

theorem tupleProdCount_succ {k D : ℕ} :
    tupleProdCount (k + 1) D = ∑ e ∈ Nat.divisors D, tupleProdCount k (D / e) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · rw [hD0, Nat.divisors_zero, Finset.sum_empty]
    simp only [tupleProdCount]
    rw [Finset.card_eq_zero]
    ext d
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hd
    have h0 := (Fintype.mem_piFinset.mp hd.1) 0
    rw [Finset.mem_Icc] at h0
    omega
  · have hD1 : 1 ≤ D := hDpos
    -- The defining finset and its first-coordinate fibers.
    set S := (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 D)).filter
      (fun d => ∏ i, d i = D) with hS
    have hmaps : ∀ d ∈ S, d 0 ∈ Finset.Icc 1 D := by
      intro d hd
      rw [hS] at hd
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hd
      exact hd.1 0
    have hcard : S.card = ∑ e ∈ Finset.Icc 1 D,
        (S.filter (fun d => d 0 = e)).card := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
    -- Fiber cards.
    have hfib : ∀ e ∈ Finset.Icc 1 D, (S.filter (fun d => d 0 = e)).card
        = if e ∣ D then tupleProdCount k (D / e) else 0 := by
      intro e he
      rw [Finset.mem_Icc] at he
      by_cases hdiv : e ∣ D
      · rw [if_pos hdiv]
        have hepos : 0 < e := by
          rcases Nat.eq_zero_or_pos e with he0 | hepos
          · omega
          · exact hepos
        have heD : e ≤ D := Nat.le_of_dvd hDpos hdiv
        have hDe : D / e * e = D := Nat.div_mul_cancel hdiv
        have hDe1 : 1 ≤ D / e := by
          rw [Nat.le_div_iff_mul_le hepos]
          simpa using heD
        -- Bijection: tail / cons.
        have hbij : (S.filter (fun d => d 0 = e)).card
            = ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 (D / e))).filter
              (fun t => ∏ i, t i = D / e)).card := by
          apply Finset.card_bij (fun d _ => Fin.tail d)
          · intro d hd
            rw [Finset.mem_filter] at hd ⊢
            obtain ⟨hdS, hd0⟩ := hd
            rw [hS, Finset.mem_filter, Fintype.mem_piFinset] at hdS
            obtain ⟨hdmem, hdprod⟩ := hdS
            have htailprod : ∏ i, Fin.tail d i = D / e := by
              have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
              rw [hd0, hdprod] at h1
              have h2 : e * ∏ i, Fin.tail d i = e * (D / e) := by
                rw [← h1, Nat.mul_div_cancel' hdiv]
              exact Nat.eq_of_mul_eq_mul_left hepos h2
            refine ⟨?_, htailprod⟩
            rw [Fintype.mem_piFinset]
            intro i
            rw [Finset.mem_Icc]
            have hmem : d i.succ ∈ Finset.Icc 1 D := hdmem i.succ
            rw [Finset.mem_Icc] at hmem
            refine ⟨hmem.1, ?_⟩
            have hdvd : d i.succ ∣ ∏ j, Fin.tail d j :=
              Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
            rw [htailprod] at hdvd
            exact Nat.le_of_dvd (by omega : 0 < D / e) hdvd
          · intro d hd e' hd' hde'
            rw [Finset.mem_filter] at hd hd'
            obtain ⟨-, hd0⟩ := hd
            obtain ⟨-, he'0⟩ := hd'
            have hd_eq : d = Fin.cons e (Fin.tail d) := by
              rw [← hd0]; exact (Fin.cons_self_tail d).symm
            have he'_eq : e' = Fin.cons e (Fin.tail e') := by
              rw [← he'0]; exact (Fin.cons_self_tail e').symm
            rw [hd_eq, he'_eq, hde']
          · intro t ht
            rw [Finset.mem_filter, Fintype.mem_piFinset] at ht
            obtain ⟨htmem, htprod⟩ := ht
            refine ⟨Fin.cons e t, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨?_, ?_⟩
              · rw [hS, Finset.mem_filter, Fintype.mem_piFinset]
                refine ⟨?_, ?_⟩
                · intro i
                  refine Fin.cases ?_ ?_ i
                  · rw [Fin.cons_zero]
                    exact Finset.mem_Icc.mpr ⟨he.1, heD⟩
                  · intro j
                    rw [Fin.cons_succ]
                    have hmi := htmem j
                    rw [Finset.mem_Icc] at hmi ⊢
                    exact ⟨hmi.1, le_trans hmi.2 (Nat.div_le_self D e)⟩
                · rw [Fin.prod_univ_succ, Fin.cons_zero]
                  simp only [Fin.cons_succ]
                  rw [htprod, Nat.mul_div_cancel' hdiv]
              · rw [Fin.cons_zero]
            · rw [Fin.tail_cons]
        rw [hbij]
        rfl
      · rw [if_neg hdiv]
        rw [Finset.card_eq_zero]
        ext d
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        intro hd
        obtain ⟨hdS, hd0⟩ := hd
        rw [hS, Finset.mem_filter] at hdS
        obtain ⟨-, hdprod⟩ := hdS
        have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
        rw [hd0, hdprod] at h1
        exact hdiv ⟨∏ i, Fin.tail d i, h1⟩
    have hTS : tupleProdCount (k + 1) D = S.card := rfl
    rw [hTS, hcard]
    rw [Finset.sum_congr rfl hfib]
    rw [← Finset.sum_filter]
    congr 1

theorem pairwise_coprime_of_squarefree_prod {k : ℕ} {d : Fin k → ℕ}
    (_hd1 : ∀ i, 1 ≤ d i) (hsq : Squarefree (∏ i, d i))
    {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (d i) (d j) := by
  have hjerase : d j ∣ ∏ i' ∈ Finset.univ.erase i, d i' :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  have hprod : ∏ i', d i' = d i * ∏ i' ∈ Finset.univ.erase i, d i' :=
    (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)).symm
  have hmul : d i * d j ∣ ∏ i', d i' := by
    rw [hprod]
    exact mul_dvd_mul_left (d i) hjerase
  have hg1 : Nat.gcd (d i) (d j) ∣ d i := Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (d i) (d j) ∣ d j := Nat.gcd_dvd_right _ _
  have hgg : Nat.gcd (d i) (d j) * Nat.gcd (d i) (d j) ∣ ∏ i', d i' :=
    dvd_trans (mul_dvd_mul hg1 hg2) hmul
  have hu : IsUnit (Nat.gcd (d i) (d j)) := hsq _ hgg
  exact Nat.isUnit_iff.mp hu

theorem prod_dvd_of_pairwise_coprime :
    ∀ {k : ℕ} {d : Fin k → ℕ} {L : ℕ},
      (∀ i j, i ≠ j → Nat.Coprime (d i) (d j)) →
      (∀ i, d i ∣ L) → ∏ i, d i ∣ L := by
  intro k
  induction k with
  | zero =>
    intro d L _ _
    simp
  | succ k ih =>
    intro d L hcop hdvd
    rw [Fin.prod_univ_succ]
    have hcop_tail : ∀ i j, i ≠ j → Nat.Coprime (Fin.tail d i) (Fin.tail d j) :=
      fun i j hij => hcop i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))
    have hdvd_tail : ∀ i, Fin.tail d i ∣ L := fun i => hdvd i.succ
    have htail : ∏ i, Fin.tail d i ∣ L := ih hcop_tail hdvd_tail
    have hcop0 : Nat.Coprime (d 0) (∏ i, Fin.tail d i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i _
      exact hcop 0 i.succ (Fin.succ_ne_zero i).symm
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop0 (hdvd 0) htail

theorem card_filter_tupleSupport_prod_le {k R D : ℕ} :
    ((tupleSupport k R).filter (fun d => ∏ i, d i = D)).card
      ≤ tupleProdCount k D := by
  apply Finset.card_le_card
  intro d hd
  rw [Finset.mem_filter] at hd
  obtain ⟨hdmem, hprod⟩ := hd
  obtain ⟨h1, -, -⟩ := mem_tupleSupport.mp hdmem
  rw [Finset.mem_filter]
  refine ⟨?_, hprod⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  refine ⟨h1 i, ?_⟩
  have hle : d i ≤ ∏ j, d j :=
    Finset.single_le_prod' (fun j _ => h1 j) (Finset.mem_univ i)
  rw [hprod] at hle
  exact hle

/-- Summing `τ_k` over the divisors of `L` gives `τ_{k+1}(L)`: the
    convolution identity plus the divisor involution `D ↦ L / D`. -/

theorem sum_tupleProdCount_divisors {k L : ℕ} (hL : L ≠ 0) :
    ∑ D ∈ L.divisors, tupleProdCount k D = tupleProdCount (k + 1) L := by
  rw [tupleProdCount_succ]
  apply Finset.sum_bij (fun D _ => L / D)
  · intro D hD
    rw [Nat.mem_divisors] at hD ⊢
    exact ⟨⟨D, (Nat.div_mul_cancel hD.1).symm⟩, hL⟩
  · intro a ha b hb hab
    rw [Nat.mem_divisors] at ha hb
    have h1 : a = L / (L / a) := (Nat.div_div_self ha.1 hL).symm
    have h2 : b = L / (L / b) := (Nat.div_div_self hb.1 hL).symm
    rw [h1, h2, hab]
  · intro D hD
    rw [Nat.mem_divisors] at hD
    refine ⟨L / D, ?_, ?_⟩
    · rw [Nat.mem_divisors]
      exact ⟨⟨D, (Nat.div_mul_cancel hD.1).symm⟩, hL⟩
    · exact Nat.div_div_self hD.1 hL
  · intro D hD
    rw [Nat.div_div_self (Nat.mem_divisors.mp hD).1 hL]

/-- The Selberg fiber count at `L`: support pairs, good at `i`,
    combined modulus `L`, both products squarefree. -/

noncomputable def fiberCountSelberg {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (i : Fin k) (L : ℕ) : ℕ :=
  ((tupleSupport k R ×ˢ tupleSupport k R).filter
    (fun p => goodPair h p.1 p.2 i ∧
      Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
      Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card

/-- The Selberg fiber count at `L` is at most `τ_{k+1}(L)²`. -/

theorem fiberCountSelberg_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (i : Fin k) (L : ℕ) :
    fiberCountSelberg h R i L ≤ tupleProdCount (k + 1) L ^ 2 := by
  by_cases hL0 : L = 0
  · subst hL0
    have hempty : fiberCountSelberg h R i 0 = 0 := by
      rw [fiberCountSelberg, Finset.card_eq_zero]
      ext p
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      intro hp
      obtain ⟨hprodmem, -, hF, -, -⟩ := hp
      have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).1
      have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).2
      obtain ⟨hd1, -, -⟩ := mem_tupleSupport.mp hp1
      obtain ⟨he1, -, -⟩ := mem_tupleSupport.mp hp2
      have hFne : Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) ≠ 0 := by
        apply Finset.lcm_ne_zero_iff.mpr
        intro j _
        apply Nat.lcm_ne_zero
        · have hj := hd1 j
          omega
        · have hj := he1 j
          omega
      exact hFne hF
    rw [hempty]
    exact Nat.zero_le _
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
    -- Each fiber pair has both products dividing L.
    have hprod_dvd : ∀ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
          Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j)),
        (∏ j, p.1 j) ∣ L ∧ (∏ j, p.2 j) ∣ L := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hprodmem, -, hF, hsq1, hsq2⟩ := hp
      have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).1
      have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).2
      obtain ⟨hd1, -, -⟩ := mem_tupleSupport.mp hp1
      obtain ⟨he1, -, -⟩ := mem_tupleSupport.mp hp2
      constructor
      · apply prod_dvd_of_pairwise_coprime
          (fun a b hab => pairwise_coprime_of_squarefree_prod hd1 hsq1 hab)
        intro j
        rw [← hF]
        exact dvd_trans (Nat.dvd_lcm_left (p.1 j) (p.2 j))
          (Finset.dvd_lcm (Finset.mem_univ j))
      · apply prod_dvd_of_pairwise_coprime
          (fun a b hab => pairwise_coprime_of_squarefree_prod he1 hsq2 hab)
        intro j
        rw [← hF]
        exact dvd_trans (Nat.dvd_lcm_right (p.1 j) (p.2 j))
          (Finset.dvd_lcm (Finset.mem_univ j))
    -- The fiber sits inside the product of the one-sided divisor fibers.
    have hsub : ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
          Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j)))
        ⊆ (tupleSupport k R).filter (fun d => ∏ j, d j ∣ L) ×ˢ
          (tupleSupport k R).filter (fun e => ∏ j, e j ∣ L) := by
      intro p hp
      obtain ⟨hdvd1, hdvd2⟩ := hprod_dvd p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hprodmem, -⟩ := hp
      have hp1 : p.1 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).1
      have hp2 : p.2 ∈ tupleSupport k R := (Finset.mem_product.mp hprodmem).2
      rw [Finset.mem_product]
      exact ⟨Finset.mem_filter.mpr ⟨hp1, hdvd1⟩, Finset.mem_filter.mpr ⟨hp2, hdvd2⟩⟩
    -- One-sided count: fiberwise over divisors, then the τ identity.
    have hone : ∀ (s : Finset (Fin k → ℕ)),
        s = (tupleSupport k R).filter (fun d => ∏ j, d j ∣ L) →
        s.card ≤ tupleProdCount (k + 1) L := by
      intro s hs
      rw [hs]
      have hmaps : ∀ d ∈ (tupleSupport k R).filter (fun d => ∏ j, d j ∣ L),
          (∏ j, d j) ∈ L.divisors := by
        intro d hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.mpr ⟨hd.2, hL0⟩
      calc ((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).card
          = ∑ D ∈ L.divisors,
              (((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).filter
                (fun d => ∏ j, d j = D)).card :=
            Finset.card_eq_sum_card_fiberwise hmaps
        _ ≤ ∑ D ∈ L.divisors, tupleProdCount k D := by
            apply Finset.sum_le_sum
            intro D _
            calc (((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).filter
                    (fun d => ∏ j, d j = D)).card
                ≤ ((tupleSupport k R).filter (fun d => ∏ j, d j = D)).card := by
                  apply Finset.card_le_card
                  intro d hd
                  rw [Finset.mem_filter] at hd
                  obtain ⟨hd1, hd2⟩ := hd
                  rw [Finset.mem_filter]
                  exact ⟨(Finset.mem_filter.mp hd1).1, hd2⟩
              _ ≤ tupleProdCount k D := card_filter_tupleSupport_prod_le
        _ = tupleProdCount (k + 1) L := sum_tupleProdCount_divisors hL0
    calc fiberCountSelberg h R i L
        = ((tupleSupport k R ×ˢ tupleSupport k R).filter
            (fun p => goodPair h p.1 p.2 i ∧
              Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
              Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card := rfl
      _ ≤ ((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L) ×ˢ
            (tupleSupport k R).filter (fun e => ∏ j, e j ∣ L)).card :=
          Finset.card_le_card hsub
      _ = ((tupleSupport k R).filter (fun d => ∏ j, d j ∣ L)).card
            * ((tupleSupport k R).filter (fun e => ∏ j, e j ∣ L)).card :=
          Finset.card_product _ _
      _ ≤ tupleProdCount (k + 1) L * tupleProdCount (k + 1) L :=
          Nat.mul_le_mul (hone _ rfl) (hone _ rfl)
      _ = tupleProdCount (k + 1) L ^ 2 := (pow_two _).symm

theorem one_sub_pow_expand (t : ℝ) (deg : ℕ) :
    (1 - t) ^ deg = ∑ j ∈ Finset.range (deg + 1),
      (deg.choose j : ℝ) * (-t) ^ j := by
  have h1 : (1 - t) ^ deg = ∑ k ∈ Finset.range (deg + 1),
      (deg.choose k : ℝ) * (-t) ^ (deg - k) := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, one_mul, mul_comm]
  rw [h1]
  rw [← Finset.sum_range_reflect
    (fun j => (deg.choose j : ℝ) * (-t) ^ j) (deg + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkk : k ≤ deg := by omega
  have hdeg : deg + 1 - 1 - k = deg - k := by omega
  rw [hdeg, Nat.choose_symm hkk]

/-- On the support, the Selberg weight is a finite monomial sum in
    `log D`: `λ_d = ∑_{j ≤ deg} (deg.choose j) * μ(D) * (-log D/log R)^j`. -/

theorem lamSelberg_expand {k R deg : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ tupleSupport k R) :
    lamSelberg k R deg d = ∑ j ∈ Finset.range (deg + 1),
      (deg.choose j : ℝ) * (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (-(Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R)) ^ j := by
  rw [lamSelberg_eq_of_mem_support hd, one_sub_pow_expand]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def monomialPairSum (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if goodPair h d e i then
      (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
    else 0

/-- Four-fold sum commutation: move the monomial indices outside the
    pair sums. -/

theorem sum_comm4 {α γ : Type*} {s : Finset α} {t : Finset γ}
    (F : α → α → γ → γ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := by
  have h1 : ∀ d : α, (∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ e ∈ s, ∑ b ∈ t, F d e a b := by
    intro d
    exact Finset.sum_comm
  have h2 : (∑ d ∈ s, ∑ e ∈ s, ∑ a ∈ t, ∑ b ∈ t, F d e a b)
      = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b := by
    calc _ = ∑ d ∈ s, ∑ a ∈ t, ∑ e ∈ s, ∑ b ∈ t, F d e a b :=
          Finset.sum_congr rfl (fun d _ => h1 d)
      _ = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b :=
          Finset.sum_comm
  have h3 : ∀ a : γ, (∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b)
      = ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := by
    intro a
    calc _ = ∑ d ∈ s, ∑ b ∈ t, ∑ e ∈ s, F d e a b := by
          apply Finset.sum_congr rfl
          intro d _
          exact Finset.sum_comm
      _ = ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b := Finset.sum_comm
  calc _ = ∑ a ∈ t, ∑ d ∈ s, ∑ e ∈ s, ∑ b ∈ t, F d e a b := h2
    _ = ∑ a ∈ t, ∑ b ∈ t, ∑ d ∈ s, ∑ e ∈ s, F d e a b :=
        Finset.sum_congr rfl (fun a _ => h3 a)

/-- The exact decomposition of the Selberg singular sum into monomial
    pair sums. This is the honest replacement for an Euler product:
    each monomial piece is a Dirichlet-type sum over good pairs, and
    its evaluation (multinomial prime expansion, Mertens-type
    estimates, local factors) is the remaining analytic core. -/

theorem singSum_selberg_expand {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i := by
  have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (if goodPair h d e i then lamSelberg k R deg d * lamSelberg k R deg e
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0) := by
    intro d hd e he
    by_cases hg : goodPair h d e i
    · rw [if_pos hg]
      rw [lamSelberg_expand hd, lamSelberg_expand he, Finset.sum_mul_sum]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      rw [if_pos hg]
      ring
    · rw [if_neg hg]
      simp only [if_neg hg, mul_zero, Finset.sum_const_zero]
  have h2 : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
      (if goodPair h d e i then lamSelberg k R deg d * lamSelberg k R deg e
        / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0))
      = ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0) :=
    Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))
  have hfactor : ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
           else 0))
      = (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i := by
    intro a _ b _
    unfold monomialPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  unfold singSum
  rw [h2, sum_comm4]
  exact Finset.sum_congr rfl
    (fun a ha => Finset.sum_congr rfl (fun b hb => hfactor a ha b hb))

noncomputable def monomialPairSumAtL (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) : ℝ :=
  ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
    if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
      ∧ goodPair h d e i)
    then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
        * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
        * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
        * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
    else 0

/-- The monomial sum grouped by combined modulus, mirroring
    `singSum_eq_sum_over_L`: the level bound `L ≤ R²` (from
    `lcm_le_sq_of_mem_support`) keeps the modulus range finite and
    inside the BV range. -/

theorem monomialPairSum_eq_sum_over_L {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    monomialPairSum k h R a b i
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  have hmem : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
        ∈ Finset.Icc 1 (R ^ 2) := by
    intro d hd e he
    obtain ⟨h1, -, -⟩ := mem_tupleSupport.mp hd
    obtain ⟨h1', -, -⟩ := mem_tupleSupport.mp he
    have hLne : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≠ 0 := by
      apply Finset.lcm_ne_zero_iff.mpr
      intro j _
      apply Nat.lcm_ne_zero
      · have hj := h1 j
        omega
      · have hj := h1' j
        omega
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hLne, lcm_le_sq_of_mem_support hd he⟩
  have hstep1 : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      (if goodPair h d e i then
        (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
       else 0)
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0) := by
    intro d hd e he
    rw [Finset.sum_ite_eq', if_pos (hmem d hd e he)]
  have hstep3 : ∀ L ∈ Finset.Icc 1 (R ^ 2),
      (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0))
      = (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
    intro L _
    have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
        (if L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) then
          (if goodPair h d e i then
            (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              / ((Nat.totient L : ℕ) : ℝ) else 0) else 0)
        = (1 / ((Nat.totient L : ℕ) : ℝ)) *
          (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
      intro d _ e _
      by_cases hLe : L = Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      · by_cases hg : goodPair h d e i
        · rw [if_pos hLe, if_pos hg, if_pos ⟨hLe.symm, hg⟩,
            mul_comm (1 / ((Nat.totient L : ℕ) : ℝ)) _, mul_one_div]
        · rw [if_pos hLe, if_neg hg, if_neg (fun hcon => hg hcon.2), mul_zero]
      · rw [if_neg hLe, if_neg (fun hcon => hLe hcon.1.symm), mul_zero]
    rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))]
    unfold monomialPairSumAtL
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  unfold monomialPairSum
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hstep1 d hd e he))]
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl (fun L hL => hstep3 L hL)

/-- The Selberg singular sum in fully grouped form: binomial
    coefficients times the modulus-grouped monomial sums. This is the
    exact identity the Mertens-type evaluation starts from. -/

theorem squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le (Squarefree.natFactorization_le_one p ha)
    (Squarefree.natFactorization_le_one p hb)

/-- The lcm of a finite family of squarefree numbers is squarefree,
    via `Finset.factorization_lcm`: the factorization of the lcm is
    the finset sup of the factorizations, each `≤ 1`. -/

theorem squarefree_finset_lcm {ι : Type*} {s : Finset ι} {g : ι → ℕ}
    (h0 : ∀ j ∈ s, g j ≠ 0) (hsq : ∀ j ∈ s, Squarefree (g j)) :
    Squarefree (s.lcm g) := by
  apply Nat.squarefree_of_factorization_le_one (Finset.lcm_ne_zero_iff.mpr h0)
  intro p
  rw [Finset.factorization_lcm h0 p]
  apply Finset.sup_le
  intro j hj
  exact Squarefree.natFactorization_le_one p (hsq j hj)

/-- The pair sum at modulus `L` vanishes unless `L` is squarefree:
    a non-squarefree combined modulus forces some coordinate lcm to
    be non-squarefree (contrapositive of `squarefree_finset_lcm`),
    hence some coordinate, hence some product, to be non-squarefree,
    killing the Möbius factor. So the grouped sum is a sum over
    squarefree moduli only. -/

theorem monomialPairSumAtL_eq_zero_of_not_squarefree {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) {L : ℕ} (hL : ¬ Squarefree L) :
    monomialPairSumAtL k h R a b i L = 0 := by
  unfold monomialPairSumAtL
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  by_cases hcon : (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
    ∧ goodPair h d e i)
  · rw [if_pos hcon]
    obtain ⟨hd1, -, -⟩ := mem_tupleSupport.mp hd
    obtain ⟨he1, -, -⟩ := mem_tupleSupport.mp he
    have hLnsq : ¬ Squarefree (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) := by
      rw [hcon.1]
      exact hL
    have h0 : ∀ j ∈ (Finset.univ : Finset (Fin k)), Nat.lcm (d j) (e j) ≠ 0 := by
      intro j _
      apply Nat.lcm_ne_zero
      · have hj := hd1 j
        omega
      · have hj := he1 j
        omega
    have hex : ∃ j, ¬ Squarefree (Nat.lcm (d j) (e j)) := by
      by_contra hnone
      push Not at hnone
      exact hLnsq (squarefree_finset_lcm h0 (fun j _ => hnone j))
    obtain ⟨j, hj⟩ := hex
    by_cases hdjsq : Squarefree (d j)
    · have hejsq : ¬ Squarefree (e j) := fun hh => hj (squarefree_lcm hdjsq hh)
      have hE : ¬ Squarefree (∏ j, e j) := fun hsq =>
        hejsq (hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem (fun j => e j) (Finset.mem_univ j)))
      have hmu : (ArithmeticFunction.moebius (∏ j, e j) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hE
      rw [hmu]
      simp
    · have hD : ¬ Squarefree (∏ j, d j) := fun hsq =>
        hdjsq (hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem (fun j => d j) (Finset.mem_univ j)))
      have hmu : (ArithmeticFunction.moebius (∏ j, d j) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hD
      rw [hmu]
      simp
  · rw [if_neg hcon]

theorem abel_sum (a f : ℕ → ℝ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (n + 1), a i * f i
      = (∑ i ∈ Finset.range (n + 1), a i) * f n
        - ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := Finset.sum_range_succ (fun i => a i * f i) (n + 1)
    have h2 := Finset.sum_range_succ (fun i => a i) (n + 1)
    have h3 := Finset.sum_range_succ
      (fun i => (∑ j ∈ Finset.range (i + 1), a j) * (f (i + 1) - f i)) n
    rw [h1, h2, h3, ih]
    ring

theorem singSum_selberg_grouped {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  rw [singSum_selberg_expand]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [monomialPairSum_eq_sum_over_L]

noncomputable def goodCountAtL {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (i : Fin k)
    (D E L : ℕ) : ℕ :=
  ((tupleSupport k R ×ˢ tupleSupport k R).filter
    (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
      Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L)).card

/-- Regrouping of the per-modulus monomial piece by products: the
    μ/log-power factor depends only on `(D, E)`, so it factors out
    of the fiber sum, leaving exactly `goodCountAtL`. -/

noncomputable def mertensWeight (D : ℕ) : ℝ :=
  if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
    / ((Nat.totient D : ℕ) : ℝ) else 0

/-- The one-variable μ²/φ-type log-power sum: `∑_{D ≤ T}
    μ²(D)/φ(D) · (log D)^m`, in range form so `abel_sum` applies
    directly. -/

noncomputable def mertensMuSqSum (m : ℕ) (T : ℕ) : ℝ :=
  ∑ D ∈ Finset.range (T + 1), mertensWeight D * (Real.log (D : ℝ)) ^ m

/-- Abel transform of the Mertens sum into partial-sum form: the
    form in which Mertens-type estimates plug in (they bound the
    partial sums `∑_{D ≤ i} μ²(D)/φ(D)`; Abel converts). -/

theorem monomialPairSumAtL_abs_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) (hR : 2 ≤ R) :
    abs (monomialPairSumAtL k h R a b i L) ≤ (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
  classical
  have hlog : ∀ d ∈ tupleSupport k R,
      abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ≤ 1 := by
    intro d hd
    obtain ⟨h1, -, h3⟩ := mem_tupleSupport.mp hd
    have hD1 : 1 ≤ ∏ j, d j := Finset.one_le_prod' (fun j _ => h1 j)
    have hDpos : (0 : ℝ) < ((∏ j, d j : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hD1)
    have hlogR : (0 : ℝ) < Real.log (R : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    have hnn : (0 : ℝ) ≤ Real.log ((∏ j, d j : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hD1)
    have hle : Real.log ((∏ j, d j : ℕ) : ℝ) ≤ Real.log (R : ℝ) :=
      Real.log_le_log hDpos (by exact_mod_cast h3)
    have hfrac0 : (0 : ℝ) ≤ Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log (R : ℝ) :=
      div_nonneg hnn hlogR.le
    have hfrac1 : Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log (R : ℝ) ≤ 1 :=
      (div_le_one hlogR).mpr hle
    rw [abs_neg, abs_of_nonneg hfrac0]
    exact hfrac1
  have hterm : ∀ d ∈ tupleSupport k R, ∀ e ∈ tupleSupport k R,
      abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
          ∧ goodPair h d e i)
        then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
            * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
            * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
            * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
        else 0)
      ≤ (if goodPair h d e i
          ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
          ∧ Squarefree (∏ j, d j) ∧ Squarefree (∏ j, e j)
        then (1 : ℝ) else 0) := by
    intro d hd e he
    by_cases hfib : goodPair h d e i
        ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
        ∧ Squarefree (∏ j, d j) ∧ Squarefree (∏ j, e j)
    · rw [if_pos hfib]
      obtain ⟨hgood, hlcm, -, -⟩ := hfib
      rw [if_pos ⟨hlcm, hgood⟩]
      have hmuD : abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ)) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hmuE : abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ)) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hlogD : abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ≤ 1 :=
        hlog d hd
      have hlogE : abs (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ≤ 1 :=
        hlog e he
      have hp1 : abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
          * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ)) ≤ 1 := by
        calc abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
              * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
            ≤ 1 * 1 := mul_le_mul hmuD hmuE (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hp2 : abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
          * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
          * (abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R))) ^ a ≤ 1 := by
        calc abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
              * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
              * (abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R))) ^ a
            ≤ 1 * 1 := mul_le_mul hp1 (pow_le_one₀ (abs_nonneg _) hlogD)
              (pow_nonneg (abs_nonneg _) _) zero_le_one
          _ = 1 := one_mul 1
      calc abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b)
          = abs ((ArithmeticFunction.moebius (∏ j, d j) : ℝ))
              * abs ((ArithmeticFunction.moebius (∏ j, e j) : ℝ))
              * (abs (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R))) ^ a
              * (abs (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R))) ^ b := by
            simp only [abs_mul, abs_pow]
        _ ≤ 1 * 1 := mul_le_mul hp2 (pow_le_one₀ (abs_nonneg _) hlogE)
            (pow_nonneg (abs_nonneg _) _) zero_le_one
        _ = 1 := one_mul 1
    · rw [if_neg hfib]
      by_cases hatl : (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
          ∧ goodPair h d e i)
      · rw [if_pos hatl]
        have hnsq : ¬ Squarefree (∏ j, d j) ∨ ¬ Squarefree (∏ j, e j) := by
          by_contra hc
          push Not at hc
          exact hfib ⟨hatl.2, hatl.1, hc.1, hc.2⟩
        rcases hnsq with hD | hE
        · have hmu : (ArithmeticFunction.moebius (∏ j, d j) : ℝ) = 0 := by
            exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hD
          rw [hmu]
          simp
        · have hmu : (ArithmeticFunction.moebius (∏ j, e j) : ℝ) = 0 := by
            exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hE
          rw [hmu]
          simp
      · rw [if_neg hatl]
        simp
  have step1 : abs (monomialPairSumAtL k h R a b i L)
      ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
    unfold monomialPairSumAtL
    exact le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _))
  have step2 : (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
        abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
            ∧ goodPair h d e i)
          then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
              * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0))
      ≤ (fiberCountSelberg h R i L : ℝ) := by
    calc (∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            abs (if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                ∧ goodPair h d e i)
              then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                  * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                  * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                  * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
              else 0))
        ≤ ∑ d ∈ tupleSupport k R, ∑ e ∈ tupleSupport k R,
            (if goodPair h d e i
                ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                ∧ Squarefree (∏ j, d j) ∧ Squarefree (∏ j, e j)
              then (1 : ℝ) else 0) :=
          Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hterm d hd e he))
      _ = (fiberCountSelberg h R i L : ℝ) := by
          rw [← Finset.sum_product', Finset.sum_boole]
          rfl
  have hcard : (fiberCountSelberg h R i L : ℝ)
      ≤ (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
    exact_mod_cast fiberCountSelberg_le h R i L
  exact le_trans (le_trans step1 step2) hcard

/-- The whole monomial sum is bounded by the finite τ²-sum over the
    modulus range (using `1/φ(L) ≤ 1` for `L ≥ 1`). -/

theorem monomialPairSum_abs_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (hR : 2 ≤ R) :
    abs (monomialPairSum k h R a b i)
      ≤ ∑ L ∈ Finset.Icc 1 (R ^ 2), (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
  rw [monomialPairSum_eq_sum_over_L]
  calc abs (∑ L ∈ Finset.Icc 1 (R ^ 2),
          (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L)
      ≤ ∑ L ∈ Finset.Icc 1 (R ^ 2),
          abs ((1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ L ∈ Finset.Icc 1 (R ^ 2), (tupleProdCount (k + 1) L : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro L hL
        rw [Finset.mem_Icc] at hL
        have hφpos : (0 : ℝ) < ((Nat.totient L : ℕ) : ℝ) := by
          exact_mod_cast (Nat.totient_pos.mpr (show 0 < L by omega))
        have hφ0 : (0 : ℝ) ≤ 1 / ((Nat.totient L : ℕ) : ℝ) :=
          div_nonneg zero_le_one hφpos.le
        have hφ1 : 1 / ((Nat.totient L : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one hφpos]
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
            (Nat.totient_pos.mpr (show 0 < L by omega)).ne')
        rw [abs_mul, abs_of_nonneg hφ0]
        calc (1 / ((Nat.totient L : ℕ) : ℝ)) * abs (monomialPairSumAtL k h R a b i L)
            ≤ 1 * (tupleProdCount (k + 1) L : ℝ) ^ 2 :=
              mul_le_mul hφ1 (monomialPairSumAtL_abs_le h R a b i L hR)
                (abs_nonneg _) zero_le_one
          _ = (tupleProdCount (k + 1) L : ℝ) ^ 2 := one_mul _

theorem singSum_selberg_grouped_squarefree {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    singSum k h R (lamSelberg k R deg) i
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ (Finset.Icc 1 (R ^ 2)).filter (fun L => Squarefree L),
            (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
  rw [singSum_selberg_grouped]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hinner : (∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L)
      = ∑ L ∈ (Finset.Icc 1 (R ^ 2)).filter (fun L => Squarefree L),
        (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro L hL hnf
    have hnsq : ¬ Squarefree L := by
      intro hsq
      exact hnf (Finset.mem_filter.mpr ⟨hL, hsq⟩)
    rw [monomialPairSumAtL_eq_zero_of_not_squarefree h R a b i hnsq]
    simp
  rw [hinner]

theorem monomialPairSumAtL_eq_goodCount_sum {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) (L : ℕ) :
    monomialPairSumAtL k h R a b i L
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (goodCountAtL h R i D E L : ℝ) := by
  classical
  have hmaps : ∀ p ∈ tupleSupport k R ×ˢ tupleSupport k R,
      (∏ j, p.1 j, ∏ j, p.2 j) ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨h1, -, h3⟩ := mem_tupleSupport.mp hp1
    obtain ⟨h1', -, h3'⟩ := mem_tupleSupport.mp hp2
    rw [Finset.mem_product]
    change (∏ j, p.1 j) ∈ Finset.Icc 1 R ∧ (∏ j, p.2 j) ∈ Finset.Icc 1 R
    constructor <;> rw [Finset.mem_Icc]
    · exact ⟨Finset.one_le_prod' (fun j _ => h1 j), h3⟩
    · exact ⟨Finset.one_le_prod' (fun j _ => h1' j), h3'⟩
  have hfib : (∑ p ∈ tupleSupport k R ×ˢ tupleSupport k R,
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0))
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E)),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  have hinner : ∀ D ∈ Finset.Icc 1 R, ∀ E ∈ Finset.Icc 1 R,
      (∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E)),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0))
      = (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (goodCountAtL h R i D E L : ℝ) := by
    intro D _ E _
    have hfilter : (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E))
        = (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E) := by
      apply Finset.filter_congr
      intro p _
      simp [Prod.mk.injEq]
    rw [hfilter]
    have hterm : ∀ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0)
        = (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
            * (-(Real.log (D : ℝ) / Real.log R)) ^ a
            * (-(Real.log (E : ℝ) / Real.log R)) ^ b
            * (if goodPair h p.1 p.2 i
                ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
              then (1 : ℝ) else 0) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨-, hD, hE⟩ := hp
      by_cases hcond : goodPair h p.1 p.2 i
          ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
      · rw [if_pos hcond, if_pos ⟨hcond.2, hcond.1⟩, hD, hE]
        ring
      · rw [if_neg hcond, if_neg (fun hcon => hcond ⟨hcon.2, hcon.1⟩)]
        simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_boole]
    congr 1
    have hcard : ((tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E)).filter
          (fun p => goodPair h p.1 p.2 i
            ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L)
        = (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
            Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      simp only [and_assoc]
    rw [hcard]
    rfl
  calc monomialPairSumAtL k h R a b i L
      = ∑ p ∈ tupleSupport k R ×ˢ tupleSupport k R,
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := by
        unfold monomialPairSumAtL
        exact (Finset.sum_product' (s := tupleSupport k R) (t := tupleSupport k R)
          (f := fun d e => if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
              ∧ goodPair h d e i)
            then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
            else 0)).symm
    _ = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        ∑ p ∈ (tupleSupport k R ×ˢ tupleSupport k R).filter
          (fun p => (∏ j, p.1 j, ∏ j, p.2 j) = (D, E)),
        (if (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L
            ∧ goodPair h p.1 p.2 i)
          then (ArithmeticFunction.moebius (∏ j, p.1 j) : ℝ)
              * (ArithmeticFunction.moebius (∏ j, p.2 j) : ℝ)
              * (-(Real.log ((∏ j, p.1 j : ℕ) : ℝ) / Real.log R)) ^ a
              * (-(Real.log ((∏ j, p.2 j : ℕ) : ℝ) / Real.log R)) ^ b
          else 0) := hfib
    _ = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (goodCountAtL h R i D E L : ℝ) :=
        Finset.sum_congr rfl (fun D hD => Finset.sum_congr rfl (fun E hE => hinner D hD E hE))

theorem mertensMuSqSum_abel (m : ℕ) (T : ℕ) :
    mertensMuSqSum m T
      = (∑ D ∈ Finset.range (T + 1), mertensWeight D) * (Real.log (T : ℝ)) ^ m
        - ∑ i ∈ Finset.range T,
            (∑ D ∈ Finset.range (i + 1), mertensWeight D)
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m) := by
  unfold mertensMuSqSum
  exact abel_sum mertensWeight (fun D => (Real.log (D : ℝ)) ^ m) T

/-- Specification of the exact Mertens-type input still needed
    (gap piece (2) in the header): the μ²/φ log-power sum is a
    constant `C m` times `(log T)^(m+1)`, up to an explicit error
    `err m T`. The constant function `C` is a parameter here —
    its exact value (from the local Euler factors) is part of what
    the Mertens pass must establish, and is NOT asserted by this
    definition. -/

theorem singSum_selberg_cond_eval {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) (mainMono : ℕ → ℕ → ℝ) (errMono : ℕ → ℕ → ℝ)
    (hMono : ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      abs (monomialPairSum k h R a b i - mainMono a b) ≤ errMono a b) :
    abs (singSum k h R (lamSelberg k R deg) i
        - ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
            (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono a b)
      ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono a b := by
  rw [singSum_selberg_expand]
  have hsub : (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) * monomialPairSum k h R a b i)
      - (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono a b)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ)
          * (monomialPairSum k h R a b i - mainMono a b) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hsub]
  calc abs (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ)
            * (monomialPairSum k h R a b i - mainMono a b))
      ≤ ∑ a ∈ Finset.range (deg + 1),
          abs (∑ b ∈ Finset.range (deg + 1),
            (deg.choose a : ℝ) * (deg.choose b : ℝ)
              * (monomialPairSum k h R a b i - mainMono a b)) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          abs ((deg.choose a : ℝ) * (deg.choose b : ℝ)
            * (monomialPairSum k h R a b i - mainMono a b)) :=
        Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
          (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono a b := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        have hca : (0 : ℝ) ≤ (deg.choose a : ℝ) := Nat.cast_nonneg _
        have hcb : (0 : ℝ) ≤ (deg.choose b : ℝ) := Nat.cast_nonneg _
        rw [abs_mul, abs_mul, abs_of_nonneg hca, abs_of_nonneg hcb]
        exact mul_le_mul_of_nonneg_left (hMono a ha b hb) (mul_nonneg hca hcb)

theorem singSum_selberg_grouped_squarefree_restated_pub2 {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ (Finset.Icc 1 (R ^ 2)).filter (fun L => Squarefree L),
            (1 / ((Nat.totient L : ℕ) : ℝ)) *
              (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                  ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                    * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                    * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                    * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                else 0) := by
  have hmain := singSum_selberg_grouped_squarefree h R deg i
  unfold singSum lamSelberg monomialPairSumAtL tupleSupport goodPair at hmain
  exact hmain

end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
        (deg.choose a : ℝ) * (deg.choose b : ℝ) *
          ∑ L ∈ (Finset.Icc 1 (R ^ 2)).filter (fun L => Squarefree L),
            (1 / ((Nat.totient L : ℕ) : ℝ)) *
              (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
                  ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
                then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
                    * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
                    * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
                    * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
                else 0) := GPY.singSum_selberg_grouped_squarefree_restated_pub2 h R deg i
