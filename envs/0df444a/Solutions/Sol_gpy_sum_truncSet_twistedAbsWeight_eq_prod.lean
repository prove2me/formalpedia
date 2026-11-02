-- Prove2me | solution 1 for gpy_sum_truncSet_twistedAbsWeight_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T10:44:44.789169+00:00
-- url     : https://prove2.me/submissions/14c60c8f-fe74-45a0-a87d-36f33d38e5c7

/- PubAll restated solution file: Mathlib only, absolute bounds only.
   No asymptotic TwistedMertensBound main term is stated or proved here. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

def truncSet_aux (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (∏ p ∈ S, p ^ 2 + 1)).filter (fun d =>
    1 ≤ d ∧ ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2)

theorem truncSet_bound_aux {S : Finset ℕ} {d : ℕ}
    (hd1 : 1 ≤ d) (hd : ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2)
    (hS : ∀ p ∈ S, 2 ≤ p) :
    d ≤ ∏ p ∈ S, p ^ 2 := by
  have hd0 : d ≠ 0 := by omega
  have h := Nat.prod_factorization_pow_eq_self hd0
  rw [← h]
  show (∏ p ∈ d.factorization.support, p ^ d.factorization p) ≤ _
  rw [Nat.support_factorization]
  calc (∏ p ∈ d.primeFactors, p ^ d.factorization p)
      ≤ ∏ p ∈ d.primeFactors, p ^ 2 := by
        apply Finset.prod_le_prod'
        intro p hp
        have hp2 : 2 ≤ p := hS p (hd p hp).1
        exact pow_le_pow_right₀ (by omega) (hd p hp).2
    _ ≤ ∏ p ∈ S, p ^ 2 := by
        apply Finset.prod_le_prod_of_subset_of_one_le'
        · intro p hp
          exact (hd p hp).1
        · intro p hpS _
          have hp2 : 2 ≤ p := hS p hpS
          exact one_le_pow₀ (by omega)

theorem mem_truncSet_aux {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {d : ℕ} :
    d ∈ truncSet_aux S ↔ 1 ≤ d ∧ ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2 := by
  constructor
  · intro hd
    simp only [truncSet_aux, Finset.mem_filter] at hd
    exact hd.2
  · intro ⟨hd1, hd⟩
    simp only [truncSet_aux, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hd1, hd⟩
    have hb := truncSet_bound_aux hd1 hd hS
    omega

theorem not_mem_primeFactors_of_mem_truncSet_aux {S : Finset ℕ}
    (hS : ∀ p ∈ S, 2 ≤ p) {d₀ : ℕ} (hd₀ : d₀ ∈ truncSet_aux S) {q : ℕ} (hqS : q ∉ S) :
    q ∉ d₀.primeFactors := by
  intro hqmem
  exact hqS (((mem_truncSet_aux hS).mp hd₀).2 q hqmem).1

theorem factorization_eq_zero_of_mem_truncSet_aux {S : Finset ℕ}
    (hS : ∀ p ∈ S, 2 ≤ p) {d₀ : ℕ} (hd₀ : d₀ ∈ truncSet_aux S) {q : ℕ}
    (hq : q.Prime) (hqS : q ∉ S) :
    d₀.factorization q = 0 := by
  have hd0 : d₀ ≠ 0 := by
    have h1 := ((mem_truncSet_aux hS).mp hd₀).1
    omega
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hdvd
  exact not_mem_primeFactors_of_mem_truncSet_aux hS hd₀ hqS
    (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd0⟩)

theorem factorization_mul_pow_aux {d₀ q j : ℕ} (hq : q.Prime)
    (hd₀ : d₀ ≠ 0) (hqd : q ∉ d₀.primeFactors) :
    (d₀ * q ^ j).factorization q = j := by
  have hqdvd : ¬ q ∣ d₀ := by
    intro hdvd
    exact hqd (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd₀⟩)
  rw [Nat.factorization_mul hd₀ (pow_ne_zero j hq.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hqdvd, zero_add]
  simp [hq.factorization_pow]

theorem truncSet_image_insert_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) :
    truncSet_aux (insert q S)
      = (truncSet_aux S ×ˢ Finset.range 3).image (fun x : ℕ × ℕ => x.1 * q ^ x.2) := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hSq : ∀ p ∈ insert q S, 2 ≤ p := by
    intro p hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hq.two_le
    · exact hS2 p hp
  ext d
  constructor
  · intro hd
    obtain ⟨hd1, hdcond⟩ := (mem_truncSet_aux hSq).mp hd
    have hd0 : d ≠ 0 := by omega
    set v := d.factorization q with hv
    have hv3 : v < 3 := by
      by_cases hqmem : q ∈ d.primeFactors
      · have hle := (hdcond q hqmem).2
        omega
      · have h0 : d.factorization q = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (by
            intro hdvd
            exact hqmem (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd0⟩))
        omega
    have hdiv : q ^ v ∣ d := Nat.ordProj_dvd d q
    have hd0mem : d / q ^ v ∈ truncSet_aux S := by
      rw [mem_truncSet_aux hS2]
      refine ⟨?_, ?_⟩
      · by_contra hcon
        have h0' : d / q ^ v = 0 := by
          have hlt := Nat.not_le.mp hcon
          exact Nat.lt_one_iff.mp hlt
        have hmul := Nat.div_mul_cancel hdiv
        rw [h0', zero_mul] at hmul
        omega
      · intro p hp
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hpdvd : p ∣ d / q ^ v := (Nat.mem_primeFactors.mp hp).2.1
        have hdvd : p ∣ d :=
          dvd_trans hpdvd ⟨q ^ v, (Nat.div_mul_cancel hdiv).symm⟩
        have hpmem : p ∈ d.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpprime, hdvd, hd0⟩
        have hpq : p ≠ q := by
          intro hpeq
          have hqmem : q ∈ (d / q ^ v).primeFactors := by
            obtain ⟨hprime, hdvd, hd0'⟩ := Nat.mem_primeFactors.mp hp
            exact Nat.mem_primeFactors.mpr ⟨hpeq ▸ hprime, hpeq ▸ hdvd, hd0'⟩
          have hfac0 : (d / q ^ v).factorization q = 0 := by
            rw [Nat.factorization_div hdiv, Finsupp.tsub_apply]
            have hqv : (q ^ v).factorization q = v := by simp [hq.factorization_pow]
            rw [hqv, tsub_self]
          have hne : (d / q ^ v).factorization q ≠ 0 := by
            have hmem : q ∈ (d / q ^ v).factorization.support := by
              rw [Nat.support_factorization]
              exact hqmem
            exact Finsupp.mem_support_iff.mp hmem
          exact hne hfac0
        refine ⟨?_, ?_⟩
        · have hmem := (hdcond p hpmem).1
          simp only [Finset.mem_insert] at hmem
          rcases hmem with h | h
          · exact absurd h hpq
          · exact h
        · have hfac : (d / q ^ v).factorization p = d.factorization p := by
            rw [Nat.factorization_div hdiv, Finsupp.tsub_apply]
            have hqfac : (q ^ v).factorization p = 0 := by
              apply Nat.factorization_eq_zero_of_not_dvd
              intro hdvdp
              have hpqdvd : p ∣ q := hpprime.dvd_of_dvd_pow hdvdp
              exact hpq ((Nat.prime_dvd_prime_iff_eq hpprime hq).mp hpqdvd)
            rw [hqfac, tsub_zero]
          rw [hfac]
          exact (hdcond p hpmem).2
    rw [Finset.mem_image]
    refine ⟨(d / q ^ v, v), ?_, ?_⟩
    · rw [Finset.mem_product]
      exact ⟨hd0mem, Finset.mem_range.mpr hv3⟩
    · exact Nat.div_mul_cancel hdiv
  · intro hd
    rw [Finset.mem_image] at hd
    obtain ⟨⟨d₀, j⟩, hmem, hmap⟩ := hd
    rw [Finset.mem_product] at hmem
    obtain ⟨hd₀, hj⟩ := hmem
    rw [Finset.mem_range] at hj
    have hmap' : d₀ * q ^ j = d := hmap
    rw [← hmap']
    rw [mem_truncSet_aux hSq]
    have hd01 := ((mem_truncSet_aux hS2).mp hd₀).1
    have hd00 : d₀ ≠ 0 := by omega
    have hqj0 : q ^ j ≠ 0 := pow_ne_zero j hq.ne_zero
    have hd₀cond := ((mem_truncSet_aux hS2).mp hd₀).2
    have hqnot : q ∉ d₀.primeFactors :=
      not_mem_primeFactors_of_mem_truncSet_aux hS2 hd₀ hqS
    have hfacq0 : d₀.factorization q = 0 :=
      factorization_eq_zero_of_mem_truncSet_aux hS2 hd₀ hq hqS
    refine ⟨?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hqj0)
    · intro p hp
      rw [Nat.primeFactors_mul hd00 hqj0, Finset.mem_union] at hp
      rcases hp with hp | hp
      · have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        refine ⟨?_, ?_⟩
        · simp only [Finset.mem_insert]
          exact Or.inr (hd₀cond p hp).1
        · rw [Nat.factorization_mul hd00 hqj0, Finsupp.add_apply]
          have hqfac : (q ^ j).factorization p = 0 := by
            apply Nat.factorization_eq_zero_of_not_dvd
            intro hdvdp
            have hpqdvd : p ∣ q := hpprime.dvd_of_dvd_pow hdvdp
            have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hpprime hq).mp hpqdvd
            exact hqnot (hpeq ▸ hp)
          rw [hqfac, add_zero]
          exact (hd₀cond p hp).2
      · have hj0 : j ≠ 0 := by
          intro hj0
          subst hj0
          simp at hp
        have hpq : p = q := by
          have hpf : (q ^ j).primeFactors = {q} :=
            Nat.primeFactors_prime_pow hj0 hq
          rw [hpf, Finset.mem_singleton] at hp
          exact hp
        subst hpq
        refine ⟨?_, ?_⟩
        · exact Finset.mem_insert_self p S
        · rw [Nat.factorization_mul hd00 hqj0, Finsupp.add_apply, hfacq0, zero_add]
          have hqj : (p ^ j).factorization p = j := by simp [hq.factorization_pow]
          rw [hqj]
          omega

theorem sum_truncSet_insert_aux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) (F : ℕ → ℝ) :
    ∑ d ∈ truncSet_aux (insert q S), F d
      = ∑ d₀ ∈ truncSet_aux S, ∑ j ∈ Finset.range 3, F (d₀ * q ^ j) := by
  rw [truncSet_image_insert_aux hS hq hqS, Finset.sum_image]
  · rw [Finset.sum_product]
  · intro x hx y hy hxy
    have hxy' : x.1 * q ^ x.2 = y.1 * q ^ y.2 := hxy
    rw [Finset.mem_coe, Finset.mem_product] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [Finset.mem_range] at hx2 hy2
    have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
    have hx0 : x.1 ≠ 0 := by
      have h1 := ((mem_truncSet_aux hS2).mp hx1).1
      omega
    have hy0 : y.1 ≠ 0 := by
      have h1 := ((mem_truncSet_aux hS2).mp hy1).1
      omega
    have hfac : x.2 = y.2 := by
      have e1 : (x.1 * q ^ x.2).factorization q = x.2 :=
        factorization_mul_pow_aux hq hx0 (by
          intro hdvd
          exact not_mem_primeFactors_of_mem_truncSet_aux hS2 hx1 hqS hdvd)
      have e2 : (y.1 * q ^ y.2).factorization q = y.2 :=
        factorization_mul_pow_aux hq hy0 (by
          intro hdvd
          exact not_mem_primeFactors_of_mem_truncSet_aux hS2 hy1 hqS hdvd)
      rw [hxy'] at e1
      exact e1.symm.trans e2
    have h1 : x.1 = y.1 := by
      rw [hfac] at hxy'
      exact mul_right_cancel₀ (pow_ne_zero y.2 hq.ne_zero) hxy'
    exact Prod.ext h1 hfac

/-- Euler-product formula for truncated sums of a multiplicative weight. -/
theorem sum_truncSet_eq_prod_aux (w : ℕ → ℝ) (hw1 : w 1 = 1)
    (hwmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → w (m * n) = w m * w n) :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    ∑ d ∈ truncSet_aux S, w d = ∏ p ∈ S, (∑ j ∈ Finset.range 3, w (p ^ j)) := by
  intro S
  induction S using Finset.induction with
  | empty =>
    intro _
    have hset : truncSet_aux (∅ : Finset ℕ) = {1} := by
      ext d
      simp only [truncSet_aux, Finset.mem_filter, Finset.mem_range, Finset.prod_empty,
        Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, -⟩
        omega
      · intro hd
        subst hd
        refine ⟨by omega, le_refl 1, ?_⟩
        intro p hp
        rw [Nat.primeFactors_one] at hp
        exact absurd hp (Finset.notMem_empty p)
    rw [hset]
    simp [hw1]
  | @insert q S hqS ih =>
    intro hS
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hq : q.Prime := hS q (Finset.mem_insert_self q S)
    have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS' p hp).two_le
    rw [sum_truncSet_insert_aux hS' hq hqS, Finset.prod_insert hqS]
    trans (∑ d₀ ∈ truncSet_aux S, w d₀ * (∑ j ∈ Finset.range 3, w (q ^ j)))
    · apply Finset.sum_congr rfl
      intro d₀ hd₀
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hd00 : d₀ ≠ 0 := by
        have h1 := ((mem_truncSet_aux hS2).mp hd₀).1
        omega
      have hnot : ¬ q ∣ d₀ := by
        intro hdvd
        exact not_mem_primeFactors_of_mem_truncSet_aux hS2 hd₀ hqS
          (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hd00⟩)
      have hcop : Nat.Coprime d₀ (q ^ j) :=
        ((hq.coprime_iff_not_dvd.mpr hnot).symm).pow_right j
      exact hwmul hd00 (pow_ne_zero j hq.ne_zero) hcop
    · rw [← Finset.sum_mul, ih hS']
      exact mul_comm _ _

/-! ### The weight `w d = |c d| / d` and the bound `∑ w ≤ e²` -/

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

noncomputable def twistedWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  (∏ p ∈ n.primeFactors, ((localGoodChoiceFinset h i p hd he).card : ℝ))
    / ((Nat.totient n : ℕ) : ℝ)

noncomputable def twistedMuSqSum {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (m M Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n M),
    (ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n
      * (Real.log (n : ℝ)) ^ m

noncomputable def twistedAbsWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) : ℝ :=
  abs ((ArithmeticFunction.moebius n : ℝ) * twistedWeight h i hd he n)

/-- The twisted weight at `1` is `1`. -/
theorem twistedWeight_one_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] :
    twistedWeight h i hd he 1 = 1 := by
  unfold twistedWeight
  simp

/-- The twisted weight is multiplicative on coprime pairs. -/
theorem twistedWeight_mul_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    twistedWeight h i hd he (m * n)
      = twistedWeight h i hd he m * twistedWeight h i hd he n := by
  unfold twistedWeight
  have hdisj : Disjoint m.primeFactors n.primeFactors := hcop.disjoint_primeFactors
  rw [Nat.primeFactors_mul hm hn, Finset.prod_union hdisj, Nat.totient_mul hcop,
    Nat.cast_mul, div_mul_div_comm]

/-- The twisted weight at a prime: `c_p / (p - 1)`. -/
theorem twistedWeight_prime_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedWeight h i hd he p
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  unfold twistedWeight
  have hcast : ((Nat.totient p : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    push_cast
    ring
  rw [hp.primeFactors, Finset.prod_singleton, hcast]

/-- Nonnegativity of the absolute twisted weight. -/
theorem twistedAbsWeight_nonneg_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) :
    (0 : ℝ) ≤ twistedAbsWeight h i hd he n := by
  unfold twistedAbsWeight
  exact abs_nonneg _

/-- The absolute twisted weight at `1` is `1`. -/
theorem twistedAbsWeight_one_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he] :
    twistedAbsWeight h i hd he 1 = 1 := by
  unfold twistedAbsWeight
  rw [twistedWeight_one_aux, ArithmeticFunction.moebius_apply_one]
  simp

/-- The absolute twisted weight is multiplicative on coprime pairs. -/
theorem twistedAbsWeight_mul_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    twistedAbsWeight h i hd he (m * n)
      = twistedAbsWeight h i hd he m * twistedAbsWeight h i hd he n := by
  unfold twistedAbsWeight
  have hmu : ArithmeticFunction.moebius (m * n)
      = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hmuR : ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius m : ℤ) : ℝ)
        * ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
    rw [hmu]
    push_cast
    ring
  rw [hmuR, twistedWeight_mul_aux h i hd he hm hn hcop]
  simp only [abs_mul]
  ring

/-- The absolute twisted weight at a prime: `c_p / (p - 1)`. -/
theorem twistedAbsWeight_prime_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedAbsWeight h i hd he p
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  unfold twistedAbsWeight
  rw [twistedWeight_prime_aux h i hd he hp, ArithmeticFunction.moebius_apply_prime hp]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hC : (0 : ℝ) ≤ ((localGoodChoiceFinset h i p hd he).card : ℝ) :=
    Nat.cast_nonneg _
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hcast : (((-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_cast
  rw [hcast]
  rw [abs_mul, abs_neg, abs_one, one_mul,
    abs_of_nonneg (div_nonneg hC (le_of_lt hden))]

/-- The absolute twisted weight at `p²` is `0` (Möbius vanishes). -/
theorem twistedAbsWeight_prime_pow_two_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    twistedAbsWeight h i hd he (p ^ 2) = 0 := by
  unfold twistedAbsWeight
  have hmu : ArithmeticFunction.moebius (p ^ 2) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by norm_num : (2 : ℕ) ≠ 0)]
    simp
  have hmuR : ((ArithmeticFunction.moebius (p ^ 2) : ℤ) : ℝ) = 0 := by
    rw [hmu]
    simp
  rw [hmuR]
  simp

/-! ### The uniform local-count bound -/

/-- The local count is at most `(k+1)²`: the local choice finset
    is a subfinset of `univ` over `Option (Fin k) × Option (Fin k)`. -/
theorem localGoodChoice_card_le_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    ((localGoodChoiceFinset h i p hd he).card : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
  have hcard : (localGoodChoiceFinset h i p hd he).card ≤ (k + 1) * (k + 1) := by
    calc (localGoodChoiceFinset h i p hd he).card
        ≤ Finset.univ.card := Finset.card_le_univ _
      _ = (k + 1) * (k + 1) := by
          simp [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  have hcast : (((k + 1) * (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) ^ 2 := by
    push_cast
    ring
  calc ((localGoodChoiceFinset h i p hd he).card : ℝ)
      ≤ (((k + 1) * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((k : ℝ) + 1) ^ 2 := hcast

/-! ### Truncated Euler product for the absolute twisted weight -/

/-- Local sums at prime powers: `1 + c_p/(p-1)`. -/
theorem sum_twistedAbsWeight_prime_pow_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    ∑ j ∈ Finset.range 3, twistedAbsWeight h i hd he (p ^ j)
      = 1 + ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  have e0 : twistedAbsWeight h i hd he (p ^ 0) = 1 := by
    simp [twistedAbsWeight_one_aux]
  have e1 : twistedAbsWeight h i hd he (p ^ 1)
      = ((localGoodChoiceFinset h i p hd he).card : ℝ) / ((p : ℝ) - 1) := by
    rw [pow_one]
    exact twistedAbsWeight_prime_aux h i hd he hp
  have e2 : twistedAbsWeight h i hd he (p ^ 2) = 0 :=
    twistedAbsWeight_prime_pow_two_aux h i hd he hp
  rw [e0, e1, e2]
  ring

/-- TRUNCATED EULER PRODUCT. Over any prime finset `S`, the
    truncated sum of the absolute twisted weight factors exactly
    as the product of the local sums `1 + c_p/(p-1)`. -/
theorem sum_truncSet_twistedAbsWeight_eq_prod_aux {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ truncSet_aux S, twistedAbsWeight h i hd he d
      = ∏ p ∈ S, (1 + ((localGoodChoiceFinset h i p hd he).card : ℝ)
          / ((p : ℝ) - 1)) := by
  rw [sum_truncSet_eq_prod_aux (twistedAbsWeight h i hd he)
    (twistedAbsWeight_one_aux h i hd he)
    (fun hm hn hcop => twistedAbsWeight_mul_aux h i hd he hm hn hcop) S hS]
  apply Finset.prod_congr rfl
  intro p hp
  exact sum_twistedAbsWeight_prime_pow_aux h i hd he (hS p hp)

/-! ### From the truncated product to the range bound -/

/-- A number with nonzero absolute twisted weight lies in the
    truncated set over the primes `≤ T`: nonzero Möbius forces
    squarefreeness, hence exponents `≤ 1 ≤ 2` and prime factors `≤ T`. -/
theorem solution {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ (Finset.range (∏ p ∈ S, p ^ 2 + 1)).filter (fun d =>
    1 ≤ d ∧ ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2), abs ((ArithmeticFunction.moebius d : ℝ) * ((∏ p ∈ d.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient d : ℕ) : ℝ))) = ∏ p ∈ S, (1 + ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1)) :=
  sum_truncSet_twistedAbsWeight_eq_prod_aux h i hd he hS
