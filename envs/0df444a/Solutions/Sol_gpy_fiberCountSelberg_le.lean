-- Prove2me | solution 1 for gpy_fiberCountSelberg_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:27:24.287375+00:00
-- url     : https://prove2.me/submissions/03bc11dc-e9be-4bfe-8343-0e670131de8a

/- Submission file for the Prove2Me problem `gpy_fiberCountSelberg_le` (publish2 fiber batch).
   Self-contained: imports Mathlib only. Contains the verified helper
   bodies needed for the proof, with top-level `theorem solution` in the
   problem's exact binder/statement form (statement mechanically extracted
   from the restated theorem, so the two are textually identical modulo
   the theorem name). No sorry tactic, no axioms beyond the standard
   ones, no platform imports. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY

/-- The support set for tuple Selberg weights at level R: tuples of positive
    integers, each at most R, whose product is at most R. -/
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

/-- Number of ordered factorizations of `D` into `k` positive factors:
    the `k`-fold divisor function `τ_k(D)` in the form the sums need.
    (Each factor is at most `D` automatically when the product is `D`
    and all factors are positive, so `Icc 1 D` is the right range.) -/
def tupleProdCount (k : ℕ) (D : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun d => ∏ i, d i = D)).card

/-- The `k`-fold divisor function satisfies the convolution identity
    `τ_{k+1}(D) = ∑_{e ∣ D} τ_k(D/e)`: split a `(k+1)`-tuple at its
    first coordinate. -/
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

/-- A support pair `(d, e)` is GOOD at coordinate `i` when some witness
    `w` of the joint system has `w + h i` coprime to `L`: exactly the
    case where BV's main term `li/φ(L)` can describe the prime count.
    Bad pairs have count ≤ 1 by the collapse lemma. -/
def goodPair {k : ℕ} (h d e : Fin k → ℕ) (i : Fin k) : Prop :=
  ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))

/-- On squarefree-product support the coordinates are pairwise
    coprime: the gcd of two distinct coordinates squares-divides
    the product, and squarefree forces it to be `1`. -/
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

/-- If a family is pairwise coprime and every coordinate divides `L`,
    then the product divides `L` (induction on the tuple dimension). -/
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

/-- The fiber of the support over a product `D` has card at most
    `τ_k(D)`: a support tuple with product `D` has all entries
    between `1` and `D`, hence is a `k`-factorization of `D`. -/
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

theorem fiberCountSelberg_le_restated_pub2 {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (i : Fin k) (L : ℕ) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)) ×ˢ
        ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R))).filter
      (fun p : (Fin k → ℕ) × (Fin k → ℕ) => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
        Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card
      ≤ ((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card ^ 2 := by
  have hmain := fiberCountSelberg_le h R i L
  unfold fiberCountSelberg tupleSupport goodPair tupleProdCount at hmain
  exact hmain


end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (i : Fin k) (L : ℕ) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)) ×ˢ
        ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R))).filter
      (fun p : (Fin k → ℕ) × (Fin k → ℕ) => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L ∧
        Squarefree (∏ j, p.1 j) ∧ Squarefree (∏ j, p.2 j))).card
      ≤ ((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card ^ 2 := GPY.fiberCountSelberg_le_restated_pub2 h R i L
