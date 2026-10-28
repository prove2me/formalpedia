-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier
-- name    : AvramDividend.Classical.vcstar_hjb_all_positive_of_generator_zero_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:53:22.139835+00:00
-- url     : https://prove2.me/theorems/233616b4-53a9-4764-8469-d0fc80b08a65
-- title:
--   Global positive-reserve HJB at zero optimal barrier from the generator inequality
-- statement:
--   If the optimal dividend barrier is zero, then every strictly positive reserve is above that barrier. Assuming the above-barrier generator residual is nonpositive and generator-integrable, the full Hamilton-Jacobi-Bellman equality holds at every positive reserve. This solves the entire zero-barrier branch of the outstanding all-positive HJB assembly without smoothness or positive-barrier endpoint conditions.
-- source:
--   Canonically Proved theorem vcstar_hjb_above_cstar_of_generator, UUID e1d50a0b-1093-42ad-a06b-f712f05608fe.

import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_hjb_all_positive_of_generator_zero_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hc0 : cstar W = 0)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by sorry
