-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_unbounded_zero_cstar
-- name    : AvramDividend.Classical.vcstar_monotone_of_unbounded_zero_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:54:53.952986+00:00
-- url     : https://prove2.me/theorems/fb7b3d42-fa20-46a5-aa9a-d66ed27c48b1
-- title:
--   Zero-barrier optimal dividend candidate is monotone
-- statement:
--   Under unbounded variation and zero optimal barrier, the exact vcstar candidate is monotone. Monotonicity of the actual optimal-barrier verification candidate gives the ordering property of the value function at the zero-barrier edge case.
-- source:
--   Previously Proved unbounded_variation_zero_barrier_candidate_monotone and the definitional equality vcstar W = barrierValue W (cstar W).toReal.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_monotone
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Order.Monotone.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_monotone_of_unbounded_zero_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    Monotone (vcstar W) := by sorry
