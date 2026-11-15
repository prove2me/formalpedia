-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a74_negative_levy_compensated_exponential_integral_split_20261114
-- name    : AvramDividend.Classical.avram_a74_negative_levy_compensated_exponential_integral_split_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:13:08.608186+00:00
-- url     : https://prove2.me/theorems/537731b3-abe6-4248-9269-7122a7a7ec64
-- title:
--   Original negative-mark Lévy compensated exponential integral splits into Poisson deficit and finite drift
-- statement:
--   Under precisely the Bochner integrability conditions for the original negative-jump exponential deficit and standard Levy compensation mark, rewrite the negative restricted exponent integral as the uncompensated exponential deficit integral minus theta times the finite drift correction on (-1,0). This combines integral_sub and the original indicator restriction identity A73; no bounded-variation hypothesis or Gaussian companion is required.
-- source:
--   Mathlib Bochner integral_sub, integral_const_mul, Proved A73 negative-mark indicator-restriction identity. The hypothesis names make all integration steps sound for arbitrary signed integrands.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a74_negative_levy_compensated_exponential_integral_split_20261114
    (ν : Measure ℝ) (θ : ℝ)
    (hExp : IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) ν)
    (hComp : IntegrableOn
      (fun y : ℝ => y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) ν) :
    (∫ y in Iio (0 : ℝ),
      (Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) ∂ν) =
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ∂ν) -
        θ * (∫ y in Ioo (-1 : ℝ) 0, y ∂ν) := by sorry
