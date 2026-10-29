-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_stationary_dyadic_ae_positive_cauchy_ws01c
-- name    : AvramDividend.Classical.bv_actual_stationary_dyadic_ae_positive_cauchy_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:23:01.289004+00:00
-- url     : https://prove2.me/theorems/3418878e-e3f9-475e-bff5-c1046054472a
-- title:
--   Actual stationary BV dyadic deficit slope is Cauchy almost everywhere at positive times
-- statement:
--   For almost every bounded-variation Lévy path, and Lebesgue-almost every positive time in (0,1], the stationary dyadic increment deficit slopes form a Cauchy sequence. The proof combines the monotone-drift-residual real derivative Cauchy theorem with an exact quotient/coercion identity at nonnegative times. This provides the pathwise almost-everywhere hypothesis for supported-time Fubini and whole-path stationarity.
-- source:
--   Causal re-publication of failed job d993b359-e944-4b27-8949-3ef00e91b33e. Its two unavailable imports are now independently Proved: bv_positive_real_actual_quotient_formula_ws01c UUID 985d5d42-8ead-44ba-ad0e-2ccf37ab1e2b and bv_actual_deficit_ae_positive_time_cauchy_ws01c UUID b52245cc-124e-4feb-b1d6-fe7db1364c62. Exact statement/preamble and original 40-line proof work/avram_ws01c_actual_positive_stationary_cauchy_solution_direct.lean preserved.

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_bv_actual_deficit_ae_positive_time_cauchy_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_positive_real_actual_quotient_formula_ws01c

open MeasureTheory Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_actual_stationary_dyadic_ae_positive_cauchy_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        CauchySeq (fun n : ℕ =>
          X.drift -
            (X.X (Real.toNNReal t + ((1 : ℝ≥0) / 2) ^ n) ω -
              X.X (Real.toNNReal t) ω) /
                (((1 : ℝ≥0) / 2) ^ n : ℝ)) := by sorry
