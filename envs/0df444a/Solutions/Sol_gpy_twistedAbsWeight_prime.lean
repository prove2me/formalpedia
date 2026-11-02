-- Prove2me | solution 1 for gpy_twistedAbsWeight_prime
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T10:35:26.209206+00:00
-- url     : https://prove2.me/submissions/db2f7142-ff8b-4ddf-a79c-0fd92154ae7d

/- PubAll restated solution file: Mathlib only, absolute bounds only.
   No asymptotic TwistedMertensBound main term is stated or proved here. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

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
theorem solution {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {p : ℕ} (hp : p.Prime) :
    abs ((ArithmeticFunction.moebius p : ℝ) * ((∏ p ∈ p.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient p : ℕ) : ℝ))) = ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1) :=
  twistedAbsWeight_prime_aux h i hd he hp
