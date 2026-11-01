-- Prove2me | solution 1 for gpy_monomialPairSum_eq_twisted_factored
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T04:23:23.325208+00:00
-- url     : https://prove2.me/submissions/6c5776b8-ac5a-40d4-835d-35fd76089c0d

/-
  Submission file for the Prove2Me problem `gpy_monomialPairSum_eq_twisted_factored`
  (publishAll batch, fully factored joint form).

  Self-contained: imports Mathlib only. Contains the verified bodies needed
  for the theorem (support, good pairs, monomial pair sums, modulus grouping,
  good-count product formula, gcd factorization of the joint weight), the
  twisted one-variable weights, and a top-level `theorem solution` in fully
  unfolded Mathlib-only terms. No platform imports. The statement is
  unconditional.
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

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

noncomputable def coordOf {k : ℕ} (d : Fin k → ℕ) (p : ℕ) : Option (Fin k) :=
  if hex : ∃ j, p ∣ d j then some (Classical.choose hex) else none

noncomputable def piChoiceFun {k : ℕ} (s : Finset ℕ)
    (f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)) :
    ℕ → Option (Fin k) × Option (Fin k) :=
  fun p => if hp : p ∈ s then f p hp else (none, none)

noncomputable def backwardD {k : ℕ} (s : Finset ℕ)
    (Ff : ℕ → Option (Fin k) × Option (Fin k)) (j : Fin k) : ℕ :=
  ∏ p ∈ s, (if (Ff p).1 = some j then p else 1)

noncomputable def backwardE {k : ℕ} (s : Finset ℕ)
    (Ff : ℕ → Option (Fin k) × Option (Fin k)) (j : Fin k) : ℕ :=
  ∏ p ∈ s, (if (Ff p).2 = some j then p else 1)

noncomputable def crtResidue {k : ℕ} (h d e : Fin k → ℕ) (p : ℕ) : ℕ :=
  if hex : ∃ j, p ∣ Nat.lcm (d j) (e j)
  then p - h (Classical.choose hex) % p else 0

theorem mem_tupleSupport_aux {k : ℕ} {R : ℕ} {d : Fin k → ℕ} :
    d ∈ tupleSupport k R ↔
      (∀ i, 1 ≤ d i) ∧ (∀ i, d i ≤ R) ∧ ∏ i, d i ≤ R := by
  rw [tupleSupport, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (Finset.mem_Icc.mp (h1 i)).1,
      fun i => (Finset.mem_Icc.mp (h1 i)).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, h2 i⟩, h3⟩

theorem prime_dvd_lcm_aux {p m n : ℕ} (hp : Nat.Prime p) (h : p ∣ Nat.lcm m n) :
    p ∣ m ∨ p ∣ n := by
  by_contra hc
  have hc1 : ¬ p ∣ m := fun h => hc (Or.inl h)
  have hc2 : ¬ p ∣ n := fun h => hc (Or.inr h)
  have hcm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc1
  have hcn : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc2
  have hcop : Nat.Coprime p (m * n) := hcm.mul_right hcn
  have hdvd : Nat.lcm m n ∣ m * n :=
    ⟨Nat.gcd m n, (Nat.gcd_mul_lcm m n).symm.trans (mul_comm _ _)⟩
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop) (dvd_trans h hdvd)

theorem prime_dvd_finset_lcm_aux {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ s.lcm f) : ∃ j ∈ s, p ∣ f j := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.lcm_empty] at h
    have h1 := Nat.dvd_one.mp h
    have h2 := hp.one_lt
    omega
  | insert a s ha ih =>
    rw [Finset.lcm_insert] at h
    rcases prime_dvd_lcm_aux hp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨j, hj, hjf⟩ := ih h2
      exact ⟨j, Finset.mem_insert_of_mem hj, hjf⟩

theorem coprime_prime_prod_aux {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hP : ∀ q ∈ P, Nat.Prime q) (hne : ∀ q ∈ P, q ≠ p) :
    Nat.Coprime p (∏ q ∈ P, q) := by
  induction P using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact Nat.coprime_one_right p
  | insert a P ha ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hne' : ∀ q ∈ P, q ≠ p := fun q hq => hne q (Finset.mem_insert_of_mem hq)
    have hpa : Nat.Coprime p a :=
      (Nat.coprime_primes hp (hP a (Finset.mem_insert_self a P))).mpr
        ((hne a (Finset.mem_insert_self a P)).symm)
    rw [Finset.prod_insert ha]
    exact hpa.mul_right (ih hP' hne')

theorem exists_modEq_prime_finset_aux {P : Finset ℕ} (a : ℕ → ℕ)
    (hP : ∀ q ∈ P, Nat.Prime q) :
    ∃ w, ∀ q ∈ P, w ≡ a q [MOD q] := by
  induction P using Finset.induction with
  | empty =>
    exact ⟨0, fun q hq => absurd hq (Finset.notMem_empty q)⟩
  | insert p P hp ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    obtain ⟨w, hw⟩ := ih hP'
    have hpprime : Nat.Prime p := hP p (Finset.mem_insert_self p P)
    have hcop : Nat.Coprime (∏ q ∈ P, q) p := by
      apply Nat.Coprime.symm
      apply coprime_prime_prod_aux hpprime hP'
      intro q hq hqp
      subst hqp
      exact hp hq
    obtain ⟨w', hw'⟩ := Nat.chineseRemainder hcop w (a p)
    refine ⟨w', ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · exact hw'.2
    · have hqdvd : q ∣ ∏ q' ∈ P, q' := Finset.dvd_prod_of_mem _ hqP
      exact (Nat.ModEq.of_dvd hqdvd hw'.1).trans (hw q hqP)

theorem crtResidue_add_aux {k : ℕ} {h d e : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (hp : Nat.Prime p) (hj : p ∣ Nat.lcm (d j) (e j))
    (hcompat : ∀ j', p ∣ Nat.lcm (d j') (e j') → h j ≡ h j' [MOD p]) :
    crtResidue h d e p + h j ≡ 0 [MOD p] := by
  unfold crtResidue
  have hex : ∃ j', p ∣ Nat.lcm (d j') (e j') := ⟨j, hj⟩
  rw [dif_pos hex]
  have hj₀dvd : p ∣ Nat.lcm (d (Classical.choose hex)) (e (Classical.choose hex)) :=
    Classical.choose_spec hex
  have hmod : h j ≡ h (Classical.choose hex) [MOD p] := hcompat _ hj₀dvd
  have step1 : (p - h (Classical.choose hex) % p) + h j
      ≡ (p - h (Classical.choose hex) % p) + h (Classical.choose hex) [MOD p] :=
    Nat.ModEq.add_left _ hmod
  have step2 : (p - h (Classical.choose hex) % p) + h (Classical.choose hex)
      ≡ 0 [MOD p] := by
    have hr : h (Classical.choose hex) % p < p := Nat.mod_lt _ hp.pos
    have e : (p - h (Classical.choose hex) % p) + h (Classical.choose hex)
        ≡ (p - h (Classical.choose hex) % p) + (h (Classical.choose hex) % p) [MOD p] :=
      (Nat.ModEq.add_left _ (Nat.mod_modEq _ _)).symm
    have e2 : (p - h (Classical.choose hex) % p) + (h (Classical.choose hex) % p) = p :=
      Nat.sub_add_cancel (le_of_lt hr)
    rw [e2] at e
    exact e.trans ((Nat.modEq_zero_iff_dvd).mpr (dvd_refl p))
  exact step1.trans step2

theorem squarefree_of_mem_prod_aux {k : ℕ} {d : Fin k → ℕ} {j : Fin k}
    (hsq : Squarefree (∏ i, d i)) : Squarefree (d j) := by
  apply Nat.squarefree_of_factorization_le_one
  · intro h0
    exact hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  · intro q
    have hall : ∀ i ∈ (Finset.univ : Finset (Fin k)), d i ≠ 0 := by
      intro i _ hi
      exact hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hle : (d j).factorization q ≤ (∏ i, d i).factorization q := by
      rw [Nat.factorization_prod_apply hall]
      exact Finset.single_le_sum (f := fun x => (d x).factorization q)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    exact le_trans hle (Squarefree.natFactorization_le_one q hsq)

theorem squarefree_lcm_aux {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le (Squarefree.natFactorization_le_one p ha)
    (Squarefree.natFactorization_le_one p hb)

theorem goodPair_iff_local_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hsqd : Squarefree (∏ j, d j)) (hsqe : Squarefree (∏ j, e j)) :
    goodPair h d e i ↔
      ∀ p, Nat.Prime p →
        p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) →
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j', p ∣ Nat.lcm (d j') (e j') →
          h j ≡ h j' [MOD p]) ∧
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ¬ h i ≡ h j [MOD p]) := by
  have hprod_d_ne : (∏ j, d j) ≠ 0 := hsqd.ne_zero
  have hprod_e_ne : (∏ j, e j) ≠ 0 := hsqe.ne_zero
  have hd_ne : ∀ j, d j ≠ 0 :=
    fun j hj => hprod_d_ne (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have he_ne : ∀ j, e j ≠ 0 :=
    fun j hj => hprod_e_ne (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hlc_ne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 :=
    fun j => Nat.lcm_ne_zero (hd_ne j) (he_ne j)
  have hL_ne : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≠ 0 :=
    Finset.lcm_ne_zero_iff.mpr (fun j _ => hlc_ne j)
  have hlc_sq : ∀ j, Squarefree (Nat.lcm (d j) (e j)) := fun j =>
    squarefree_lcm_aux (squarefree_of_mem_prod_aux hsqd) (squarefree_of_mem_prod_aux hsqe)
  constructor
  · intro hgood p hp hpL
    unfold goodPair at hgood
    obtain ⟨w, hw, hcop⟩ := hgood
    constructor
    · intro j hj j' hj'
      have h1 : p ∣ w + h j := dvd_trans hj (hw j)
      have h2 : p ∣ w + h j' := dvd_trans hj' (hw j')
      have e1 : w + h j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h1
      have e2 : w + h j' ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h2
      have e3 : w + h j ≡ w + h j' [MOD p] := e1.trans e2.symm
      exact Nat.ModEq.add_left_cancel' _ e3
    · intro j hj hcon
      have h1 : p ∣ w + h j := dvd_trans hj (hw j)
      have e1 : w + h i ≡ w + h j [MOD p] := Nat.ModEq.add_left _ hcon
      have h2 : p ∣ w + h i :=
        Nat.modEq_zero_iff_dvd.mp (e1.trans (Nat.modEq_zero_iff_dvd.mpr h1))
      have hcop' : Nat.Coprime (w + h i) p := hcop.coprime_dvd_right hpL
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop'.symm) h2
  · intro hlocal
    have hPprime : ∀ q ∈ (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))).primeFactors,
        Nat.Prime q := fun q hq => Nat.prime_of_mem_primeFactors hq
    obtain ⟨w, hw⟩ := exists_modEq_prime_finset_aux (crtResidue h d e) hPprime
    have hwdiv : ∀ j, Nat.lcm (d j) (e j) ∣ w + h j := by
      intro j
      by_cases h0 : w + h j = 0
      · rw [h0]
        exact dvd_zero _
      · apply (Nat.factorization_le_iff_dvd (hlc_ne j) h0).mp
        refine Finsupp.le_def.mpr ?_
        intro q
        by_cases hqprime : Nat.Prime q
        · by_cases hqdvd : q ∣ Nat.lcm (d j) (e j)
          · have hle1 := Squarefree.natFactorization_le_one q (hlc_sq j)
            have hpos : 1 ≤ (Nat.lcm (d j) (e j)).factorization q :=
              (Nat.Prime.pow_dvd_iff_le_factorization hqprime (hlc_ne j)).mp
                (by rwa [pow_one])
            have hqL : q ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
              dvd_trans hqdvd (Finset.dvd_lcm (Finset.mem_univ j))
            have hqP : q ∈ (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hqprime, hqL, hL_ne⟩
            have hwq : w ≡ crtResidue h d e q [MOD q] := hw q hqP
            have hlocq := hlocal q hqprime hqL
            have hres : crtResidue h d e q + h j ≡ 0 [MOD q] :=
              crtResidue_add_aux hqprime hqdvd
                (fun j' hj' => (hlocq.1 j' hj' j hqdvd).symm)
            have hqw : q ∣ w + h j :=
              Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_right _ hwq).trans hres)
            have hpos2 : 1 ≤ (w + h j).factorization q :=
              (Nat.Prime.pow_dvd_iff_le_factorization hqprime h0).mp
                (by rwa [pow_one])
            omega
          · rw [Nat.factorization_eq_zero_of_not_dvd hqdvd]
            exact Nat.zero_le _
        · rw [Nat.factorization_eq_zero_of_not_prime _ hqprime]
          exact Nat.zero_le _
    refine ⟨w, hwdiv, ?_⟩
    by_contra hne
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : p ∣ w + h i := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have h2 : p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
      dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    obtain ⟨j, -, hj⟩ := prime_dvd_finset_lcm_aux hpprime h2
    have hloc := hlocal p hpprime h2
    apply hloc.2 j hj
    have hwj : p ∣ w + h j := dvd_trans hj (hwdiv j)
    have e1 : w + h i ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h1
    have e2 : w + h j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hwj
    have e3 : w + h i ≡ w + h j [MOD p] := e1.trans e2.symm
    exact Nat.ModEq.add_left_cancel' _ e3

theorem pairwise_coprime_of_squarefree_prod_aux {k : ℕ} {d : Fin k → ℕ}
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

theorem prod_dvd_of_pairwise_coprime_aux :
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

theorem combined_lcm_eq_aux {k : ℕ} {d e : Fin k → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) (he1 : ∀ i, 1 ≤ e i)
    (hsqd : Squarefree (∏ i, d i)) (hsqe : Squarefree (∏ i, e i)) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      = Nat.lcm (∏ i, d i) (∏ i, e i) := by
  apply dvd_antisymm
  · apply Finset.lcm_dvd
    intro j _
    apply Nat.lcm_dvd
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_right _ _)
  · apply Nat.lcm_dvd
    · apply prod_dvd_of_pairwise_coprime_aux
        (fun i j hij => pairwise_coprime_of_squarefree_prod_aux hd1 hsqd hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_left (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))
    · apply prod_dvd_of_pairwise_coprime_aux
        (fun i j hij => pairwise_coprime_of_squarefree_prod_aux he1 hsqe hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_right (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))

theorem goodPair_iff_local_of_products_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {D E : ℕ} (hD : ∏ j, d j = D) (hE : ∏ j, e j = E)
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    goodPair h d e i ↔
      ∀ p, Nat.Prime p → p ∣ Nat.lcm D E →
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j', p ∣ Nat.lcm (d j') (e j') →
          h j ≡ h j' [MOD p]) ∧
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ¬ h i ≡ h j [MOD p]) := by
  have hsqd : Squarefree (∏ j, d j) := by
    rw [hD]
    exact hsqD
  have hsqe : Squarefree (∏ j, e j) := by
    rw [hE]
    exact hsqE
  have hd1 : ∀ j, 1 ≤ d j := by
    intro j
    by_contra hc
    have hj0 : d j = 0 := by omega
    have h0 : ∏ j', d j' = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj0
    rw [hD] at h0
    exact hsqD.ne_zero h0
  have he1 : ∀ j, 1 ≤ e j := by
    intro j
    by_contra hc
    have hj0 : e j = 0 := by omega
    have h0 : ∏ j', e j' = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj0
    rw [hE] at h0
    exact hsqE.ne_zero h0
  have hcomb : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = Nat.lcm D E := by
    rw [← hD, ← hE]
    exact combined_lcm_eq_aux hd1 he1 hsqd hsqe
  rw [goodPair_iff_local_aux hsqd hsqe, hcomb]

theorem mem_localGoodChoiceFinset_aux {k : ℕ} {h : Fin k → ℕ} {i : Fin k} {p : ℕ}
    {hd he : Prop} [Decidable hd] [Decidable he]
    {ab : Option (Fin k) × Option (Fin k)} :
    ab ∈ localGoodChoiceFinset h i p hd he ↔
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]) := by
  simp only [localGoodChoiceFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem prime_dvd_finset_prod_aux {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ ∏ i ∈ s, f i) : ∃ j ∈ s, p ∣ f j := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty] at h
    exact absurd h hp.not_dvd_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨j, hj, hjf⟩ := ih h2
      exact ⟨j, Finset.mem_insert_of_mem hj, hjf⟩

theorem exists_unique_coord_of_squarefree_prod_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    (hpd : p ∣ ∏ j, d j) : ∃! j, p ∣ d j := by
  obtain ⟨j₀, -, hj₀⟩ := prime_dvd_finset_prod_aux hp hpd
  refine ⟨j₀, hj₀, ?_⟩
  intro y hy
  by_contra hne
  have hcop := pairwise_coprime_of_squarefree_prod_aux hd1 hsq hne
  have hdiv : p ∣ Nat.gcd (d y) (d j₀) := Nat.dvd_gcd hy hj₀
  have hgcd : Nat.gcd (d y) (d j₀) = 1 := hcop
  rw [hgcd] at hdiv
  exact hp.not_dvd_one hdiv

theorem coordOf_eq_some_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (h : coordOf d p = some j) : p ∣ d j := by
  unfold coordOf at h
  by_cases hex : ∃ j, p ∣ d j
  · rw [dif_pos hex] at h
    have hc : Classical.choose hex = j := Option.some.inj h
    rw [← hc]
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    simp at h

theorem coordOf_some_of_dvd_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    {j : Fin k} (hj : p ∣ d j) : coordOf d p = some j := by
  have hpd : p ∣ ∏ j, d j :=
    dvd_trans hj (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  obtain ⟨j₀, hj₀, huniq⟩ := exists_unique_coord_of_squarefree_prod_aux hd1 hsq hp hpd
  have hjj : j = j₀ := huniq j hj
  have hex : ∃ j', p ∣ d j' := ⟨j, hj⟩
  have hc : Classical.choose hex = j := by
    have h1 := Classical.choose_spec hex
    have h2 := huniq _ h1
    rw [← hjj] at h2
    exact h2
  unfold coordOf
  rw [dif_pos hex, hc]

theorem coordOf_none_of_not_dvd_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (h : ¬ ∃ j, p ∣ d j) : coordOf d p = none := by
  unfold coordOf
  rw [dif_neg h]

theorem coordOf_isSome_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ} :
    (coordOf d p).isSome ↔ ∃ j, p ∣ d j := by
  unfold coordOf
  by_cases hex : ∃ j, p ∣ d j
  · rw [dif_pos hex]
    simp [hex]
  · rw [dif_neg hex]
    simp [hex]

theorem mem_primeFactors_lcm_aux {D E p : ℕ} (hD : D ≠ 0) (hE : E ≠ 0) :
    p ∈ (Nat.lcm D E).primeFactors ↔ Nat.Prime p ∧ (p ∣ D ∨ p ∣ E) := by
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpdvd, -⟩
    refine ⟨hp, ?_⟩
    rcases prime_dvd_lcm_aux hp hpdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨hp, h | h⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left D E), Nat.lcm_ne_zero hD hE⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right D E), Nat.lcm_ne_zero hD hE⟩

theorem piChoiceFun_apply_aux {k : ℕ} {s : Finset ℕ}
    {f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)} {p : ℕ} (hp : p ∈ s) :
    piChoiceFun s f p = f p hp := by
  unfold piChoiceFun
  rw [dif_pos hp]

theorem fiber_card_eq_pi_card_aux {k : ℕ} {h : Fin k → ℕ} {R : ℕ} {i : Fin k}
    {D E : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
    (hDR : D ≤ R) (hER : E ≤ R) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R) ×ˢ
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter
      (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧
        (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E))).card
      = ((Nat.lcm D E).primeFactors.pi
          (fun p => (Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter
            (fun ab => (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
              (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
                (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
              (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card := by
  classical
  have hD0 : D ≠ 0 := hsqD.ne_zero
  have hE0 : E ≠ 0 := hsqE.ne_zero
  have hL0 : Nat.lcm D E ≠ 0 := Nat.lcm_ne_zero hD0 hE0
  have hprime : ∀ p ∈ (Nat.lcm D E).primeFactors, Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  have memF : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)) →
      de.1 ∈ tupleSupport k R ∧ de.2 ∈ tupleSupport k R ∧
      ∏ j, de.1 j = D ∧ ∏ j, de.2 j = E ∧ goodPair h de.1 de.2 i ∧
      Finset.lcm Finset.univ (fun j => Nat.lcm (de.1 j) (de.2 j)) = Nat.lcm D E := by
    intro de hde
    rw [Finset.mem_filter, Finset.mem_product] at hde
    obtain ⟨⟨h1, h2⟩, hp1, hp2, hg, hl⟩ := hde
    exact ⟨h1, h2, hp1, hp2, hg, hl⟩
  have fwd_char1 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors, ∀ j : Fin k,
        coordOf de.1 p = some j ↔ p ∣ de.1 j := by
    intro de hde p hp j
    obtain ⟨hs1, -, hp1, -, -, -⟩ := memF de hde
    have hsup1 := (mem_tupleSupport_aux.mp hs1).1
    have hsq1 : Squarefree (∏ j, de.1 j) := by rw [hp1]; exact hsqD
    constructor
    · intro hc
      exact coordOf_eq_some_aux hc
    · intro hj
      exact coordOf_some_of_dvd_aux hsup1 hsq1 (hprime p hp) hj
  have fwd_char2 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors, ∀ j : Fin k,
        coordOf de.2 p = some j ↔ p ∣ de.2 j := by
    intro de hde p hp j
    obtain ⟨-, hs2, -, hp2, -, -⟩ := memF de hde
    have hsup2 := (mem_tupleSupport_aux.mp hs2).1
    have hsq2 : Squarefree (∏ j, de.2 j) := by rw [hp2]; exact hsqE
    constructor
    · intro hc
      exact coordOf_eq_some_aux hc
    · intro hj
      exact coordOf_some_of_dvd_aux hsup2 hsq2 (hprime p hp) hj
  have fwd_isSome1 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors,
        (coordOf de.1 p).isSome ↔ p ∣ D := by
    intro de hde p hp
    obtain ⟨-, -, hp1, -, -, -⟩ := memF de hde
    rw [coordOf_isSome_aux]
    constructor
    · rintro ⟨j, hj⟩
      have hprod : p ∣ ∏ j, de.1 j :=
        dvd_trans hj (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
      rw [hp1] at hprod
      exact hprod
    · intro hpd
      have hprod : p ∣ ∏ j, de.1 j := by rw [hp1]; exact hpd
      obtain ⟨j, -, hj⟩ := prime_dvd_finset_prod_aux (hprime p hp) hprod
      exact ⟨j, hj⟩
  have fwd_isSome2 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors,
        (coordOf de.2 p).isSome ↔ p ∣ E := by
    intro de hde p hp
    obtain ⟨-, -, -, hp2, -, -⟩ := memF de hde
    rw [coordOf_isSome_aux]
    constructor
    · rintro ⟨j, hj⟩
      have hprod : p ∣ ∏ j, de.2 j :=
        dvd_trans hj (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
      rw [hp2] at hprod
      exact hprod
    · intro hpd
      have hprod : p ∣ ∏ j, de.2 j := by rw [hp2]; exact hpd
      obtain ⟨j, -, hj⟩ := prime_dvd_finset_prod_aux (hprime p hp) hprod
      exact ⟨j, hj⟩
  apply Finset.card_bij (fun de _ p _ => (coordOf de.1 p, coordOf de.2 p))
  · intro de hde
    show (fun p _ => (coordOf de.1 p, coordOf de.2 p)) ∈
      (Nat.lcm D E).primeFactors.pi
        (fun p => localGoodChoiceFinset h i p (p ∣ D) (p ∣ E))
    rw [Finset.mem_pi]
    intro p hp
    show (coordOf de.1 p, coordOf de.2 p) ∈
      localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)
    rw [mem_localGoodChoiceFinset_aux]
    obtain ⟨-, -, hp1, hp2, hg, -⟩ := memF de hde
    have hpL : p ∣ Nat.lcm D E := (Nat.mem_primeFactors.mp hp).2.1
    have hloc := (goodPair_iff_local_of_products_aux hp1 hp2 hsqD hsqE).mp hg p (hprime p hp) hpL
    refine ⟨fwd_isSome1 de hde p hp, fwd_isSome2 de hde p hp, ?_, ?_⟩
    · intro j j' hj hj'
      have hlj : p ∣ Nat.lcm (de.1 j) (de.2 j) := by
        rcases hj with hj | hj
        · exact dvd_trans ((fwd_char1 de hde p hp j).mp hj) (Nat.dvd_lcm_left _ _)
        · exact dvd_trans ((fwd_char2 de hde p hp j).mp hj) (Nat.dvd_lcm_right _ _)
      have hlj' : p ∣ Nat.lcm (de.1 j') (de.2 j') := by
        rcases hj' with hj' | hj'
        · exact dvd_trans ((fwd_char1 de hde p hp j').mp hj') (Nat.dvd_lcm_left _ _)
        · exact dvd_trans ((fwd_char2 de hde p hp j').mp hj') (Nat.dvd_lcm_right _ _)
      exact hloc.1 j hlj j' hlj'
    · intro j hj
      have hlj : p ∣ Nat.lcm (de.1 j) (de.2 j) := by
        rcases hj with hj | hj
        · exact dvd_trans ((fwd_char1 de hde p hp j).mp hj) (Nat.dvd_lcm_left _ _)
        · exact dvd_trans ((fwd_char2 de hde p hp j).mp hj) (Nat.dvd_lcm_right _ _)
      exact hloc.2 j hlj
  · intro de₁ h₁ de₂ h₂ heq
    have hpt : ∀ p (hp : p ∈ (Nat.lcm D E).primeFactors),
        coordOf de₁.1 p = coordOf de₂.1 p ∧
        coordOf de₁.2 p = coordOf de₂.2 p := by
      intro p hp
      have hfun := congrFun (congrFun heq p) hp
      exact ⟨congrArg Prod.fst hfun, congrArg Prod.snd hfun⟩
    have hpf1 : ∀ j : Fin k, (de₁.1 j).primeFactors =
        (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₁.1 p = some j) := by
      intro j
      obtain ⟨hs1, -, hp1, -, -, -⟩ := memF de₁ h₁
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpdvd : p ∣ de₁.1 j := (Nat.mem_primeFactors.mp hpm).2.1
        have hdj0 : de₁.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs1).1 j
          omega
        have hps : p ∈ (Nat.lcm D E).primeFactors := by
          rw [Nat.mem_primeFactors]
          refine ⟨hpp, ?_, hL0⟩
          have hpd : p ∣ D := by
            have h1 : p ∣ ∏ j, de₁.1 j :=
              dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
            rw [hp1] at h1
            exact h1
          exact dvd_trans hpd (Nat.dvd_lcm_left D E)
        exact ⟨hps, (fwd_char1 de₁ h₁ p hps j).mpr hpdvd⟩
      · rintro ⟨hps, hc⟩
        have hpdvd : p ∣ de₁.1 j := (fwd_char1 de₁ h₁ p hps j).mp hc
        have hdj0 : de₁.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs1).1 j
          omega
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpdvd, hdj0⟩
    have hpf2 : ∀ j : Fin k, (de₂.1 j).primeFactors =
        (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₂.1 p = some j) := by
      intro j
      obtain ⟨hs2, -, hp2, -, -, -⟩ := memF de₂ h₂
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpdvd : p ∣ de₂.1 j := (Nat.mem_primeFactors.mp hpm).2.1
        have hdj0 : de₂.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs2).1 j
          omega
        have hps : p ∈ (Nat.lcm D E).primeFactors := by
          rw [Nat.mem_primeFactors]
          refine ⟨hpp, ?_, hL0⟩
          have hpd : p ∣ D := by
            have h1 : p ∣ ∏ j, de₂.1 j :=
              dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
            rw [hp2] at h1
            exact h1
          exact dvd_trans hpd (Nat.dvd_lcm_left D E)
        exact ⟨hps, (fwd_char1 de₂ h₂ p hps j).mpr hpdvd⟩
      · rintro ⟨hps, hc⟩
        have hpdvd : p ∣ de₂.1 j := (fwd_char1 de₂ h₂ p hps j).mp hc
        have hdj0 : de₂.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs2).1 j
          omega
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpdvd, hdj0⟩
    have hcoord1 : ∀ j : Fin k, de₁.1 j = de₂.1 j := by
      intro j
      obtain ⟨-, -, hp1, -, -, -⟩ := memF de₁ h₁
      obtain ⟨-, -, hp2, -, -, -⟩ := memF de₂ h₂
      have hsq1 : Squarefree (de₁.1 j) :=
        squarefree_of_mem_prod_aux (by rw [hp1]; exact hsqD)
      have hsq2 : Squarefree (de₂.1 j) :=
        squarefree_of_mem_prod_aux (by rw [hp2]; exact hsqD)
      calc de₁.1 j = ∏ p ∈ (de₁.1 j).primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree hsq1).symm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₁.1 p = some j), p := by rw [hpf1 j]
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₂.1 p = some j), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            rw [(hpt p hp).1]
        _ = ∏ p ∈ (de₂.1 j).primeFactors, p := by rw [hpf2 j]
        _ = de₂.1 j := Nat.prod_primeFactors_of_squarefree hsq2
    have hcoord2 : ∀ j : Fin k, de₁.2 j = de₂.2 j := by
      intro j
      obtain ⟨-, -, -, hp1, -, -⟩ := memF de₁ h₁
      obtain ⟨-, -, -, hp2, -, -⟩ := memF de₂ h₂
      have hsq1 : Squarefree (de₁.2 j) :=
        squarefree_of_mem_prod_aux (by rw [hp1]; exact hsqE)
      have hsq2 : Squarefree (de₂.2 j) :=
        squarefree_of_mem_prod_aux (by rw [hp2]; exact hsqE)
      have hpf1' : (de₁.2 j).primeFactors =
          (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₁.2 p = some j) := by
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · intro hpm
          have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
          have hpdvd : p ∣ de₁.2 j := (Nat.mem_primeFactors.mp hpm).2.1
          have hdj0 : de₁.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₁ h₁).2.1).1 j
            omega
          have hps : p ∈ (Nat.lcm D E).primeFactors := by
            rw [Nat.mem_primeFactors]
            refine ⟨hpp, ?_, hL0⟩
            have hpd : p ∣ E := by
              have h1 : p ∣ ∏ j, de₁.2 j :=
                dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
              rw [hp1] at h1
              exact h1
            exact dvd_trans hpd (Nat.dvd_lcm_right D E)
          exact ⟨hps, (fwd_char2 de₁ h₁ p hps j).mpr hpdvd⟩
        · rintro ⟨hps, hc⟩
          have hpdvd : p ∣ de₁.2 j := (fwd_char2 de₁ h₁ p hps j).mp hc
          have hdj0 : de₁.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₁ h₁).2.1).1 j
            omega
          rw [Nat.mem_primeFactors]
          exact ⟨hprime p hps, hpdvd, hdj0⟩
      have hpf2' : (de₂.2 j).primeFactors =
          (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₂.2 p = some j) := by
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · intro hpm
          have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
          have hpdvd : p ∣ de₂.2 j := (Nat.mem_primeFactors.mp hpm).2.1
          have hdj0 : de₂.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₂ h₂).2.1).1 j
            omega
          have hps : p ∈ (Nat.lcm D E).primeFactors := by
            rw [Nat.mem_primeFactors]
            refine ⟨hpp, ?_, hL0⟩
            have hpd : p ∣ E := by
              have h1 : p ∣ ∏ j, de₂.2 j :=
                dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
              rw [hp2] at h1
              exact h1
            exact dvd_trans hpd (Nat.dvd_lcm_right D E)
          exact ⟨hps, (fwd_char2 de₂ h₂ p hps j).mpr hpdvd⟩
        · rintro ⟨hps, hc⟩
          have hpdvd : p ∣ de₂.2 j := (fwd_char2 de₂ h₂ p hps j).mp hc
          have hdj0 : de₂.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₂ h₂).2.1).1 j
            omega
          rw [Nat.mem_primeFactors]
          exact ⟨hprime p hps, hpdvd, hdj0⟩
      calc de₁.2 j = ∏ p ∈ (de₁.2 j).primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree hsq1).symm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₁.2 p = some j), p := by rw [hpf1']
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₂.2 p = some j), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            rw [(hpt p hp).2]
        _ = ∏ p ∈ (de₂.2 j).primeFactors, p := by rw [hpf2']
        _ = de₂.2 j := Nat.prod_primeFactors_of_squarefree hsq2
    exact Prod.ext (funext fun j => hcoord1 j) (funext fun j => hcoord2 j)
  · intro f hf
    set Ff := piChoiceFun (Nat.lcm D E).primeFactors f with hFf_def
    have hFf : ∀ p (hp : p ∈ (Nat.lcm D E).primeFactors), Ff p = f p hp := by
      intro p hp
      rw [hFf_def]
      exact piChoiceFun_apply_aux hp
    set dd := backwardD (Nat.lcm D E).primeFactors Ff with hdd_def
    set ee := backwardE (Nat.lcm D E).primeFactors Ff with hee_def
    have hFmem : ∀ p (hp : p ∈ (Nat.lcm D E).primeFactors),
        (((Ff p).1.isSome = true ↔ p ∣ D) ∧ ((Ff p).2.isSome = true ↔ p ∣ E) ∧
        (∀ j j', ((Ff p).1 = some j ∨ (Ff p).2 = some j) →
          ((Ff p).1 = some j' ∨ (Ff p).2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, ((Ff p).1 = some j ∨ (Ff p).2 = some j) →
          ¬ h i ≡ h j [MOD p])) := by
      intro p hp
      rw [hFf p hp]
      have hfm : f p hp ∈ localGoodChoiceFinset h i p (p ∣ D) (p ∣ E) := by
        have hmem := hf
        rw [Finset.mem_pi] at hmem
        exact hmem p hp
      rwa [mem_localGoodChoiceFinset_aux] at hfm
    have hdvd : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, (Ff p).1 = some j → p ∣ dd j := by
      intro p hp j hj
      have hfac : (if (Ff p).1 = some j then p else 1) = p := if_pos hj
      have hdvd0 : (if (Ff p).1 = some j then p else 1) ∣ dd j := by
        rw [hdd_def]
        show (if (Ff p).1 = some j then p else 1) ∣
          ∏ p' ∈ (Nat.lcm D E).primeFactors, (if (Ff p').1 = some j then p' else 1)
        exact Finset.dvd_prod_of_mem _ hp
      rwa [hfac] at hdvd0
    have hedvd : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, (Ff p).2 = some j → p ∣ ee j := by
      intro p hp j hj
      have hfac : (if (Ff p).2 = some j then p else 1) = p := if_pos hj
      have hdvd0 : (if (Ff p).2 = some j then p else 1) ∣ ee j := by
        rw [hee_def]
        show (if (Ff p).2 = some j then p else 1) ∣
          ∏ p' ∈ (Nat.lcm D E).primeFactors, (if (Ff p').2 = some j then p' else 1)
        exact Finset.dvd_prod_of_mem _ hp
      rwa [hfac] at hdvd0
    have hdvd_rev : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, p ∣ dd j → (Ff p).1 = some j := by
      intro p hp j hdvd
      have hpp : Nat.Prime p := hprime p hp
      have hdvd' : p ∣ ∏ p' ∈ (Nat.lcm D E).primeFactors,
          (if (Ff p').1 = some j then p' else 1) := by
        rw [hdd_def] at hdvd
        exact hdvd
      obtain ⟨p', hp', hpf⟩ := prime_dvd_finset_prod_aux hpp hdvd'
      by_cases hc : (Ff p').1 = some j
      · rw [if_pos hc] at hpf
        have hp'prime : Nat.Prime p' := hprime p' hp'
        rcases (Nat.dvd_prime hp'prime).mp hpf with h1 | h1
        · exact absurd h1 hpp.ne_one
        · rw [← h1] at hc
          exact hc
      · rw [if_neg hc] at hpf
        exact (hpp.not_dvd_one hpf).elim
    have hedvd_rev : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, p ∣ ee j → (Ff p).2 = some j := by
      intro p hp j hedvd
      have hpp : Nat.Prime p := hprime p hp
      have hedvd' : p ∣ ∏ p' ∈ (Nat.lcm D E).primeFactors,
          (if (Ff p').2 = some j then p' else 1) := by
        rw [hee_def] at hedvd
        exact hedvd
      obtain ⟨p', hp', hpf⟩ := prime_dvd_finset_prod_aux hpp hedvd'
      by_cases hc : (Ff p').2 = some j
      · rw [if_pos hc] at hpf
        have hp'prime : Nat.Prime p' := hprime p' hp'
        rcases (Nat.dvd_prime hp'prime).mp hpf with h1 | h1
        · exact absurd h1 hpp.ne_one
        · rw [← h1] at hc
          exact hc
      · rw [if_neg hc] at hpf
        exact (hpp.not_dvd_one hpf).elim
    have hfilterD : (Nat.lcm D E).primeFactors.filter (fun p => p ∣ D) = D.primeFactors := by
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hps, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpd, hD0⟩
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpd : p ∣ D := (Nat.mem_primeFactors.mp hpm).2.1
        refine ⟨?_, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hpp, dvd_trans hpd (Nat.dvd_lcm_left D E), hL0⟩
    have hfilterE : (Nat.lcm D E).primeFactors.filter (fun p => p ∣ E) = E.primeFactors := by
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hps, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpd, hE0⟩
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpd : p ∣ E := (Nat.mem_primeFactors.mp hpm).2.1
        refine ⟨?_, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hpp, dvd_trans hpd (Nat.dvd_lcm_right D E), hL0⟩
    have hprod_dd : ∏ j, dd j = D := by
      calc ∏ j, dd j
          = ∏ j, ∏ p ∈ (Nat.lcm D E).primeFactors,
              (if (Ff p).1 = some j then p else 1) := by
            apply Finset.prod_congr rfl
            intro j _
            rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, ∏ j,
              (if (Ff p).1 = some j then p else 1) := Finset.prod_comm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).1.isSome then p else 1) := by
            apply Finset.prod_congr rfl
            intro p hp
            cases hFp : (Ff p).1 with
            | none =>
              have h1 : ∀ j : Fin k,
                  (if (none : Option (Fin k)) = some j then p else 1) = 1 := by
                intro j
                exact if_neg (fun h => Option.some_ne_none j h.symm)
              rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const_one]
              rfl
            | some j₀ =>
              have h1 : ∀ b ∈ (Finset.univ : Finset (Fin k)), b ≠ j₀ →
                  (if (some j₀ : Option (Fin k)) = some b then p else 1) = 1 := by
                intro b _ hb
                exact if_neg (fun hcon => hb (Option.some.inj hcon).symm)
              have h2 : j₀ ∉ (Finset.univ : Finset (Fin k)) →
                  (if (some j₀ : Option (Fin k)) = some j₀ then p else 1) = 1 :=
                fun hcon => absurd (Finset.mem_univ j₀) hcon
              rw [Finset.prod_eq_single j₀ h1 h2, if_pos rfl]
              rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => (Ff p).1.isSome), p := by
            rw [Finset.prod_filter]
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => p ∣ D), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            exact (hFmem p hp).1
        _ = ∏ p ∈ D.primeFactors, p := by rw [hfilterD]
        _ = D := Nat.prod_primeFactors_of_squarefree hsqD
    have hprod_ee : ∏ j, ee j = E := by
      calc ∏ j, ee j
          = ∏ j, ∏ p ∈ (Nat.lcm D E).primeFactors,
              (if (Ff p).2 = some j then p else 1) := by
            apply Finset.prod_congr rfl
            intro j _
            rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, ∏ j,
              (if (Ff p).2 = some j then p else 1) := Finset.prod_comm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).2.isSome then p else 1) := by
            apply Finset.prod_congr rfl
            intro p hp
            cases hFp : (Ff p).2 with
            | none =>
              have h1 : ∀ j : Fin k,
                  (if (none : Option (Fin k)) = some j then p else 1) = 1 := by
                intro j
                exact if_neg (fun h => Option.some_ne_none j h.symm)
              rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const_one]
              rfl
            | some j₀ =>
              have h1 : ∀ b ∈ (Finset.univ : Finset (Fin k)), b ≠ j₀ →
                  (if (some j₀ : Option (Fin k)) = some b then p else 1) = 1 := by
                intro b _ hb
                exact if_neg (fun hcon => hb (Option.some.inj hcon).symm)
              have h2 : j₀ ∉ (Finset.univ : Finset (Fin k)) →
                  (if (some j₀ : Option (Fin k)) = some j₀ then p else 1) = 1 :=
                fun hcon => absurd (Finset.mem_univ j₀) hcon
              rw [Finset.prod_eq_single j₀ h1 h2, if_pos rfl]
              rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => (Ff p).2.isSome), p := by
            rw [Finset.prod_filter]
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => p ∣ E), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            exact (hFmem p hp).2.1
        _ = ∏ p ∈ E.primeFactors, p := by rw [hfilterE]
        _ = E := Nat.prod_primeFactors_of_squarefree hsqE
    have h1d : ∀ j, 1 ≤ dd j := by
      intro j
      rw [hdd_def]
      show 1 ≤ ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).1 = some j then p else 1)
      apply Finset.one_le_prod'
      intro p' hp'
      split_ifs with hc
      · exact (hprime p' hp').one_lt.le
      · exact le_refl 1
    have h1e : ∀ j, 1 ≤ ee j := by
      intro j
      rw [hee_def]
      show 1 ≤ ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).2 = some j then p else 1)
      apply Finset.one_le_prod'
      intro p' hp'
      split_ifs with hc
      · exact (hprime p' hp').one_lt.le
      · exact le_refl 1
    have hdle : ∀ j, dd j ≤ R := by
      intro j
      calc dd j ≤ ∏ j', dd j' :=
            Finset.single_le_prod' (fun j' _ => h1d j') (Finset.mem_univ j)
        _ = D := hprod_dd
        _ ≤ R := hDR
    have hele : ∀ j, ee j ≤ R := by
      intro j
      calc ee j ≤ ∏ j', ee j' :=
            Finset.single_le_prod' (fun j' _ => h1e j') (Finset.mem_univ j)
        _ = E := hprod_ee
        _ ≤ R := hER
    have hprodle_dd : ∏ j, dd j ≤ R := by rw [hprod_dd]; exact hDR
    have hprodle_ee : ∏ j, ee j ≤ R := by rw [hprod_ee]; exact hER
    have hdmem : dd ∈ tupleSupport k R := mem_tupleSupport_aux.mpr ⟨h1d, hdle, hprodle_dd⟩
    have hemem : ee ∈ tupleSupport k R := mem_tupleSupport_aux.mpr ⟨h1e, hele, hprodle_ee⟩
    have hcomb : Finset.lcm Finset.univ (fun j => Nat.lcm (dd j) (ee j)) = Nat.lcm D E := by
      have hsqd : Squarefree (∏ j, dd j) := by rw [hprod_dd]; exact hsqD
      have hsqe : Squarefree (∏ j, ee j) := by rw [hprod_ee]; exact hsqE
      calc Finset.lcm Finset.univ (fun j => Nat.lcm (dd j) (ee j))
          = Nat.lcm (∏ j, dd j) (∏ j, ee j) := combined_lcm_eq_aux h1d h1e hsqd hsqe
        _ = Nat.lcm D E := by rw [hprod_dd, hprod_ee]
    have hgood : goodPair h dd ee i := by
      apply (goodPair_iff_local_of_products_aux hprod_dd hprod_ee hsqD hsqE).mpr
      intro p hp hpL
      have hps : p ∈ (Nat.lcm D E).primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpL, hL0⟩
      obtain ⟨-, -, hcompat, hnoncong⟩ := hFmem p hps
      constructor
      · intro j hlj j' hlj'
        apply hcompat j j'
        · rcases prime_dvd_lcm_aux hp hlj with hd | he
          · exact Or.inl (hdvd_rev p hps j hd)
          · exact Or.inr (hedvd_rev p hps j he)
        · rcases prime_dvd_lcm_aux hp hlj' with hd | he
          · exact Or.inl (hdvd_rev p hps j' hd)
          · exact Or.inr (hedvd_rev p hps j' he)
      · intro j hlj
        apply hnoncong j
        rcases prime_dvd_lcm_aux hp hlj with hd | he
        · exact Or.inl (hdvd_rev p hps j hd)
        · exact Or.inr (hedvd_rev p hps j he)
    have hmem : (dd, ee) ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)) := by
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hdmem, hemem⟩, hprod_dd, hprod_ee, hgood, hcomb⟩
    have hfwdeq : (fun p _ => (coordOf dd p, coordOf ee p)) = f := by
      funext p hp
      show (coordOf dd p, coordOf ee p) = f p hp
      rw [← hFf p hp]
      refine Prod.ext ?_ ?_
      · show coordOf dd p = (Ff p).1
        cases hFc : (Ff p).1 with
        | none =>
          apply coordOf_none_of_not_dvd_aux
          rintro ⟨j, hj⟩
          have hcon := hdvd_rev p hp j hj
          rw [hFc] at hcon
          simp at hcon
        | some j₀ =>
          exact coordOf_some_of_dvd_aux h1d
            (by rw [hprod_dd]; exact hsqD) (hprime p hp) (hdvd p hp j₀ hFc)
      · show coordOf ee p = (Ff p).2
        cases hFc : (Ff p).2 with
        | none =>
          apply coordOf_none_of_not_dvd_aux
          rintro ⟨j, hj⟩
          have hcon := hedvd_rev p hp j hj
          rw [hFc] at hcon
          simp at hcon
        | some j₀ =>
          exact coordOf_some_of_dvd_aux h1e
            (by rw [hprod_ee]; exact hsqE) (hprime p hp) (hedvd p hp j₀ hFc)
    exact ⟨(dd, ee), hmem, hfwdeq⟩

theorem goodCountAtL_eq_prod_local_aux {k : ℕ} {h : Fin k → ℕ} {R : ℕ}
    {i : Fin k} {D E : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
    (hDR : D ≤ R) (hER : E ≤ R) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R) ×ˢ
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter
      (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧
        (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E))).card
      = ∏ p ∈ (Nat.lcm D E).primeFactors,
          ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter
            (fun ab => (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
              (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
                (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
              (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card := by
  rw [fiber_card_eq_pi_card_aux hsqD hsqE hDR hER]
  exact Finset.card_pi _ _

theorem goodCountAtL_eq_if_prod_local_inlined_aux {k : ℕ} {h : Fin k → ℕ} {R : ℕ}
    {i : Fin k} {D E L : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
    (hDR : D ≤ R) (hER : E ≤ R) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R) ×ˢ
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter
      (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧
        (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L))).card
      = if L = Nat.lcm D E then
          ∏ p ∈ (Nat.lcm D E).primeFactors,
            ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter
              (fun ab => (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
                (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
                  (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
                (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card
        else 0 := by
  by_cases hL : L = Nat.lcm D E
  · rw [if_pos hL, hL]
    exact goodCountAtL_eq_prod_local_aux hsqD hsqE hDR hER
  · rw [if_neg hL]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro de hde
    rw [Finset.mem_filter, Finset.mem_product] at hde
    obtain ⟨⟨hs1, hs2⟩, hp1, hp2, -, hlc⟩ := hde
    have hsq1 : Squarefree (∏ j, de.1 j) := by rw [hp1]; exact hsqD
    have hsq2 : Squarefree (∏ j, de.2 j) := by rw [hp2]; exact hsqE
    have h1 := (mem_tupleSupport_aux.mp hs1).1
    have h2 := (mem_tupleSupport_aux.mp hs2).1
    have hcomb := combined_lcm_eq_aux h1 h2 hsq1 hsq2
    rw [hp1, hp2] at hcomb
    exact hL (hlc.symm.trans hcomb)


noncomputable def jointWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (D E : ℕ) : ℝ :=
  (∏ p ∈ (Nat.lcm D E).primeFactors,
    ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
    / ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ)

theorem goodCountAtL_eq_if_prod_local_aux {k : ℕ} {h : Fin k → ℕ} {R : ℕ} {i : Fin k}
    {D E L : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
    (hDR : D ≤ R) (hER : E ≤ R) :
    goodCountAtL h R i D E L
      = if L = Nat.lcm D E then
          ∏ p ∈ (Nat.lcm D E).primeFactors,
            (localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card
        else 0 :=
  goodCountAtL_eq_if_prod_local_inlined_aux hsqD hsqE hDR hER

theorem monomialPairSum_eq_joint_sum_aux {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    monomialPairSum k h R a b i
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * jointWeight h i D E := by
  classical
  rw [monomialPairSum_eq_sum_over_L]
  have hexpand : ∀ L ∈ Finset.Icc 1 (R ^ 2),
      (1 / ((Nat.totient L : ℕ) : ℝ)) * monomialPairSumAtL k h R a b i L
        = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
          (1 / ((Nat.totient L : ℕ) : ℝ))
            * ((ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
              * (-(Real.log (D : ℝ) / Real.log R)) ^ a
              * (-(Real.log (E : ℝ) / Real.log R)) ^ b
              * (goodCountAtL h R i D E L : ℝ)) := by
    intro L _
    rw [monomialPairSumAtL_eq_goodCount_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hexpand]
  have hswap : (∑ L ∈ Finset.Icc 1 (R ^ 2), ∑ D ∈ Finset.Icc 1 R,
        ∑ E ∈ Finset.Icc 1 R,
        (1 / ((Nat.totient L : ℕ) : ℝ))
          * ((ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
            * (-(Real.log (D : ℝ) / Real.log R)) ^ a
            * (-(Real.log (E : ℝ) / Real.log R)) ^ b
            * (goodCountAtL h R i D E L : ℝ)))
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ))
          * ((ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
            * (-(Real.log (D : ℝ) / Real.log R)) ^ a
            * (-(Real.log (E : ℝ) / Real.log R)) ^ b
            * (goodCountAtL h R i D E L : ℝ)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    exact Finset.sum_comm
  rw [hswap]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro E hE
  rw [Finset.mem_Icc] at hD hE
  have hfactor : (∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ))
          * ((ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
            * (-(Real.log (D : ℝ) / Real.log R)) ^ a
            * (-(Real.log (E : ℝ) / Real.log R)) ^ b
            * (goodCountAtL h R i D E L : ℝ)))
      = ((ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b)
        * (∑ L ∈ Finset.Icc 1 (R ^ 2),
          (1 / ((Nat.totient L : ℕ) : ℝ)) * (goodCountAtL h R i D E L : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L _
    ring
  rw [hfactor]
  by_cases hsqD : Squarefree D
  · by_cases hsqE : Squarefree E
    · have hinner : (∑ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) * (goodCountAtL h R i D E L : ℝ))
          = jointWeight h i D E := by
        have hterm : ∀ L ∈ Finset.Icc 1 (R ^ 2),
            (1 / ((Nat.totient L : ℕ) : ℝ)) * (goodCountAtL h R i D E L : ℝ)
              = if L = Nat.lcm D E then
                  (1 / ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ))
                    * (∏ p ∈ (Nat.lcm D E).primeFactors,
                        ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
                else 0 := by
          intro L _
          rw [goodCountAtL_eq_if_prod_local_aux hsqD hsqE hD.2 hE.2]
          by_cases hL : L = Nat.lcm D E
          · rw [if_pos hL, if_pos hL, hL, Nat.cast_prod]
          · rw [if_neg hL, if_neg hL, Nat.cast_zero, mul_zero]
        have hmem : Nat.lcm D E ∈ Finset.Icc 1 (R ^ 2) := by
          rw [Finset.mem_Icc]
          have hD0 : D ≠ 0 := hsqD.ne_zero
          have hE0 : E ≠ 0 := hsqE.ne_zero
          constructor
          · exact Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero hD0 hE0)
          · calc Nat.lcm D E = Nat.lcm D E * 1 := (mul_one _).symm
              _ ≤ Nat.lcm D E * Nat.gcd D E :=
                  mul_le_mul (le_refl _) (Nat.one_le_iff_ne_zero.mpr
                    (Nat.ne_of_gt (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left D E)
                      (by omega : 0 < D)))) (Nat.zero_le _) (Nat.zero_le _)
              _ = D * E := (Nat.mul_comm _ _).trans (Nat.gcd_mul_lcm D E)
              _ ≤ R * R := mul_le_mul hD.2 hE.2 (Nat.zero_le _) (Nat.zero_le _)
              _ = R ^ 2 := (pow_two R).symm
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hmem]
        unfold jointWeight
        rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]
        exact mul_comm _ _
      rw [hinner]
    · have hmu : (ArithmeticFunction.moebius E : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqE
      rw [hmu]
      simp
  · have hmu : (ArithmeticFunction.moebius D : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqD
    rw [hmu]
    simp


theorem sq_not_dvd_both_aux {n d : ℕ} (hsq : Squarefree n) (hd : d ∣ n)
    {p : ℕ} (hp : p.Prime) : ¬ (p ∣ d ∧ p ∣ n / d) := by
  rintro ⟨h1, h2⟩
  have hpp : p * p ∣ n := by
    have hnm : n = (n / d) * d := (Nat.div_mul_cancel hd).symm
    rw [hnm]
    exact mul_dvd_mul h2 h1
  have hunit : IsUnit p := hsq p hpp
  rw [Nat.isUnit_iff] at hunit
  subst hunit
  exact Nat.not_prime_one hp

theorem coprime_div_of_squarefree_aux {n d : ℕ} (hsq : Squarefree n)
    (hd : d ∣ n) : Nat.Coprime (n / d) d := by
  show Nat.gcd (n / d) d = 1
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : p ∣ n / d := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  exact sq_not_dvd_both_aux hsq hd hp ⟨h2, h1⟩



theorem primeFactors_lcm_split_aux {D E : ℕ} (hD0 : D ≠ 0) (hE0 : E ≠ 0) :
    (Nat.lcm D E).primeFactors
      = (Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors
        ∪ (E / Nat.gcd D E).primeFactors := by
  have hdvdD : Nat.gcd D E ∣ D := Nat.gcd_dvd_left D E
  have hdvdE : Nat.gcd D E ∣ E := Nat.gcd_dvd_right D E
  have hD1dvd : D / Nat.gcd D E ∣ D :=
    ⟨Nat.gcd D E, (Nat.div_mul_cancel hdvdD).symm⟩
  have hE1dvd : E / Nat.gcd D E ∣ E :=
    ⟨Nat.gcd D E, (Nat.div_mul_cancel hdvdE).symm⟩
  have hgdpos : 0 < Nat.gcd D E :=
    Nat.pos_of_dvd_of_pos hdvdD (Nat.pos_of_ne_zero hD0)
  have hgdne : Nat.gcd D E ≠ 0 := Nat.ne_of_gt hgdpos
  have hD1ne : D / Nat.gcd D E ≠ 0 := by
    intro h
    have h2 := Nat.div_mul_cancel hdvdD
    rw [h, Nat.zero_mul] at h2
    exact hD0 h2.symm
  have hE1ne : E / Nat.gcd D E ≠ 0 := by
    intro h
    have h2 := Nat.div_mul_cancel hdvdE
    rw [h, Nat.zero_mul] at h2
    exact hE0 h2.symm
  ext p
  rw [mem_primeFactors_lcm_aux hD0 hE0]
  simp only [Finset.mem_union, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hpp, hpD | hpE⟩
    · have h : p ∣ Nat.gcd D E ∨ p ∣ D / Nat.gcd D E := by
        have hDD : D = Nat.gcd D E * (D / Nat.gcd D E) :=
          (Nat.mul_div_cancel' hdvdD).symm
        rw [hDD] at hpD
        exact hpp.dvd_mul.mp hpD
      rcases h with h1 | h1
      · exact Or.inl (Or.inl ⟨hpp, h1, hgdne⟩)
      · exact Or.inl (Or.inr ⟨hpp, h1, hD1ne⟩)
    · have h : p ∣ Nat.gcd D E ∨ p ∣ E / Nat.gcd D E := by
        have hEE : E = Nat.gcd D E * (E / Nat.gcd D E) :=
          (Nat.mul_div_cancel' hdvdE).symm
        rw [hEE] at hpE
        exact hpp.dvd_mul.mp hpE
      rcases h with h1 | h1
      · exact Or.inl (Or.inl ⟨hpp, h1, hgdne⟩)
      · exact Or.inr ⟨hpp, h1, hE1ne⟩
  · intro hmem
    rcases hmem with hAB | hC
    · rcases hAB with hA | hB
      · exact ⟨hA.1, Or.inl (dvd_trans hA.2.1 hdvdD)⟩
      · exact ⟨hB.1, Or.inl (dvd_trans hB.2.1 hD1dvd)⟩
    · exact ⟨hC.1, Or.inr (dvd_trans hC.2.1 hE1dvd)⟩

theorem primeFactors_gcd_disjoint_left_aux {D E : ℕ} (hsqD : Squarefree D) :
    Disjoint (Nat.gcd D E).primeFactors (D / Nat.gcd D E).primeFactors := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [Nat.mem_primeFactors] at hp1 hp2
  exact sq_not_dvd_both_aux hsqD (Nat.gcd_dvd_left D E) hp1.1 ⟨hp1.2.1, hp2.2.1⟩

theorem primeFactors_gcd_disjoint_right_aux {D E : ℕ} (hsqD : Squarefree D)
    (hsqE : Squarefree E) :
    Disjoint ((Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors)
      (E / Nat.gcd D E).primeFactors := by
  rw [Finset.disjoint_left]
  intro p hpU hpE
  simp only [Finset.mem_union, Nat.mem_primeFactors] at hpU
  rw [Nat.mem_primeFactors] at hpE
  rcases hpU with hp1 | hp1
  · exact sq_not_dvd_both_aux hsqE (Nat.gcd_dvd_right D E) hp1.1 ⟨hp1.2.1, hpE.2.1⟩
  · have hpD : p ∣ D :=
      dvd_trans hp1.2.1 ⟨Nat.gcd D E, (Nat.div_mul_cancel (Nat.gcd_dvd_left D E)).symm⟩
    have hpE' : p ∣ E :=
      dvd_trans hpE.2.1 ⟨Nat.gcd D E, (Nat.div_mul_cancel (Nat.gcd_dvd_right D E)).symm⟩
    have hpg : p ∣ Nat.gcd D E := Nat.dvd_gcd hpD hpE'
    exact sq_not_dvd_both_aux hsqD (Nat.gcd_dvd_left D E) hp1.1 ⟨hpg, hp1.2.1⟩

theorem jointWeight_factor_aux {k : ℕ} {h : Fin k → ℕ} {i : Fin k} {D E : ℕ}
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    jointWeight h i D E
      = ((∏ p ∈ (Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
            / ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (D / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
            / ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (E / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
            / ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ)) := by
  classical
  have hD0 : D ≠ 0 := hsqD.ne_zero
  have hE0 : E ≠ 0 := hsqE.ne_zero
  have hdD : Nat.gcd D E ∣ D := Nat.gcd_dvd_left D E
  have hdE : Nat.gcd D E ∣ E := Nat.gcd_dvd_right D E
  have hgdpos : 0 < Nat.gcd D E :=
    Nat.pos_of_dvd_of_pos hdD (Nat.pos_of_ne_zero hD0)
  have hDD : D = Nat.gcd D E * (D / Nat.gcd D E) := (Nat.mul_div_cancel' hdD).symm
  have hEE : E = Nat.gcd D E * (E / Nat.gcd D E) := (Nat.mul_div_cancel' hdE).symm
  have hlcm : Nat.lcm D E
      = Nat.gcd D E * ((D / Nat.gcd D E) * (E / Nat.gcd D E)) := by
    apply Nat.eq_of_mul_eq_mul_left hgdpos
    calc Nat.gcd D E * Nat.lcm D E = D * E := Nat.gcd_mul_lcm D E
      _ = (Nat.gcd D E * (D / Nat.gcd D E)) * (Nat.gcd D E * (E / Nat.gcd D E)) := by
          rw [← hDD, ← hEE]
      _ = Nat.gcd D E * (Nat.gcd D E * ((D / Nat.gcd D E) * (E / Nat.gcd D E))) := by
          ring
  have hφ : ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ)
      = ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ)
        * ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ)
        * ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ) := by
    rw [hlcm]
    have hc1 : Nat.Coprime (Nat.gcd D E)
        ((D / Nat.gcd D E) * (E / Nat.gcd D E)) := by
      apply Nat.Coprime.mul_right
      · exact (coprime_div_of_squarefree_aux hsqD hdD).symm
      · exact (coprime_div_of_squarefree_aux hsqE hdE).symm
    have hc2 : Nat.Coprime (D / Nat.gcd D E) (E / Nat.gcd D E) :=
      Nat.coprime_div_gcd_div_gcd hgdpos
    rw [Nat.totient_mul hc1, Nat.totient_mul hc2]
    push_cast
    ring
  have hprod : (∏ p ∈ (Nat.lcm D E).primeFactors,
        ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
      = (∏ p ∈ (Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
        * (∏ p ∈ (D / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
        * (∏ p ∈ (E / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ)) := by
    rw [primeFactors_lcm_split_aux hD0 hE0,
      Finset.prod_union (primeFactors_gcd_disjoint_right_aux hsqD hsqE),
      Finset.prod_union (primeFactors_gcd_disjoint_left_aux hsqD)]
  unfold jointWeight
  rw [hprod, hφ]
  ring


noncomputable def twistedWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  (∏ p ∈ n.primeFactors, ((localGoodChoiceFinset h i p hd he).card : ℝ))
    / ((Nat.totient n : ℕ) : ℝ)

theorem localGoodChoiceFinset_card_congr_aux {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} {hd he hd' he' : Prop} [Decidable hd] [Decidable he]
    [Decidable hd'] [Decidable he'] (h1 : hd ↔ hd') (h2 : he ↔ he') :
    (localGoodChoiceFinset h i p hd he).card
      = (localGoodChoiceFinset h i p hd' he').card := by
  unfold localGoodChoiceFinset
  congr 1
  apply Finset.filter_congr
  intro ab _
  simp only [h1, h2]

theorem monomialPairSum_eq_twisted_factored_aux {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    monomialPairSum k h R a b i
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (twistedWeight h i True True (Nat.gcd D E)
            * twistedWeight h i True False (D / Nat.gcd D E)
            * twistedWeight h i False True (E / Nat.gcd D E)) := by
  classical
  rw [monomialPairSum_eq_joint_sum_aux]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro E hE
  rw [Finset.mem_Icc] at hD hE
  by_cases hsqD : Squarefree D
  · by_cases hsqE : Squarefree E
    · have hfactor := jointWeight_factor_aux (k := k) (h := h) (i := i)
        (D := D) (E := E) hsqD hsqE
      have hdD : Nat.gcd D E ∣ D := Nat.gcd_dvd_left D E
      have hdE : Nat.gcd D E ∣ E := Nat.gcd_dvd_right D E
      have hD1dvd : D / Nat.gcd D E ∣ D :=
        ⟨Nat.gcd D E, (Nat.div_mul_cancel hdD).symm⟩
      have hE1dvd : E / Nat.gcd D E ∣ E :=
        ⟨Nat.gcd D E, (Nat.div_mul_cancel hdE).symm⟩
      have hconv1 : (∏ p ∈ (Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
          = ∏ p ∈ (Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p True True).card : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpD : p ∣ D :=
          dvd_trans (Nat.mem_primeFactors.mp hp).2.1 hdD
        have hpE : p ∣ E :=
          dvd_trans (Nat.mem_primeFactors.mp hp).2.1 hdE
        rw [localGoodChoiceFinset_card_congr_aux (iff_of_true hpD trivial) (iff_of_true hpE trivial)]
      have hconv2 : (∏ p ∈ (D / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
          = ∏ p ∈ (D / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p True False).card : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hpD : p ∣ D := dvd_trans (Nat.mem_primeFactors.mp hp).2.1 hD1dvd
        have hpE : ¬ p ∣ E := by
          intro hpE
          have hpg : p ∣ Nat.gcd D E := Nat.dvd_gcd hpD hpE
          exact sq_not_dvd_both_aux hsqD hdD hpp ⟨hpg, (Nat.mem_primeFactors.mp hp).2.1⟩
        rw [localGoodChoiceFinset_card_congr_aux (iff_of_true hpD trivial) (iff_of_false hpE (fun h => h))]
      have hconv3 : (∏ p ∈ (E / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
          = ∏ p ∈ (E / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p False True).card : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hpE : p ∣ E := dvd_trans (Nat.mem_primeFactors.mp hp).2.1 hE1dvd
        have hpD : ¬ p ∣ D := by
          intro hpD
          have hpg : p ∣ Nat.gcd D E := Nat.dvd_gcd hpD hpE
          exact sq_not_dvd_both_aux hsqE hdE hpp ⟨hpg, (Nat.mem_primeFactors.mp hp).2.1⟩
        rw [localGoodChoiceFinset_card_congr_aux (iff_of_false hpD (fun h => h)) (iff_of_true hpE trivial)]
      rw [hfactor]
      unfold twistedWeight
      rw [hconv1, hconv2, hconv3]
    · have hmu : (ArithmeticFunction.moebius E : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqE
      rw [hmu]
      simp
  · have hmu : (ArithmeticFunction.moebius D : ℝ) = 0 := by
      exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsqD
    rw [hmu]
    simp

end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (a b : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
          Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
        (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
          * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
          * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
          * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
          / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
      else 0)
      = ∑ D ∈ Finset.Icc 1 R, ∑ E ∈ Finset.Icc 1 R,
        (ArithmeticFunction.moebius D : ℝ) * (ArithmeticFunction.moebius E : ℝ)
          * (-(Real.log (D : ℝ) / Real.log R)) ^ a
          * (-(Real.log (E : ℝ) / Real.log R)) ^ b
          * (((∏ p ∈ (Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ True) ∧ (ab.2.isSome ↔ True) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
            / ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ))
            * ((∏ p ∈ (D / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ True) ∧ (ab.2.isSome ↔ False) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
            / ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ))
            * ((∏ p ∈ (E / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ False) ∧ (ab.2.isSome ↔ True) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
            / ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ))) :=
  GPY.monomialPairSum_eq_twisted_factored_aux h R a b i
