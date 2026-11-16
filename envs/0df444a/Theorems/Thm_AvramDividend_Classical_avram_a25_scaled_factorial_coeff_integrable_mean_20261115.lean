-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_scaled_factorial_coeff_integrable_mean_20261115
-- name    : AvramDividend.Classical.avram_a25_scaled_factorial_coeff_integrable_mean_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:35:01.225652+00:00
-- url     : https://prove2.me/theorems/26894ead-abf3-4d24-976b-abee4015e756
-- title:
--   Scaled descending-factorial count coefficients are integrable and have exact exponential-series means
-- statement:
--   With positive r and all actual factorial moments E(K)_n=r^n, for any real coefficient z, each coefficient (K)_n z^n/n! is Bochner integrable and has expectation (rz)^n/n!. Uses the proved positive factorial-moment integrability lemma and integral_mul_const; no infinite-sum manipulations are involved. Essential modular component for proving the positive MGF by summation.
-- source:
--   Integrable.of_integral_ne_zero, integral_mul_const, mul_pow and polynomial arithmetic on real coefficients.

import Mathlib
open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat
noncomputable section

theorem AvramDividend.Classical.avram_a25_scaled_factorial_coeff_integrable_mean_20261115
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n)
    (z : ℝ) :
    ∀ n : ℕ,
      Integrable (fun ω =>
        (Nat.descFactorial (K ω) n : ℝ) * (z ^ n / (n.factorial : ℝ))) P ∧
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) *
          (z ^ n / (n.factorial : ℝ)) ∂P) =
        ((r : ℝ) * z) ^ n / (n.factorial : ℝ) := by sorry
