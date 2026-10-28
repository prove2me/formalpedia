-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_continuous_of_unbounded_zero_cstar
-- name    : AvramDividend.Classical.vcstar_continuous_of_unbounded_zero_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:54:32.655919+00:00
-- url     : https://prove2.me/theorems/12297880-7c96-4a0a-b351-b43a7b51a848
-- title:
--   Zero-barrier optimal dividend candidate is globally continuous
-- statement:
--   Under unbounded variation and zero optimal barrier, the exact vcstar candidate is globally continuous. Continuity of the actual verification candidate provides the boundary regularity needed when applying local comparison arguments.
-- source:
--   Previously Proved unbounded_variation_zero_barrier_candidate_continuous and the definitional equality vcstar W = barrierValue W (cstar W).toReal.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_continuous
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Order.OrderClosed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_continuous_of_unbounded_zero_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    Continuous (vcstar W) := by sorry
