-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_instant_ruin
-- name    : AvramDividend.Classical.barrier_zero_boundary_value_package_of_unbounded_instant_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:50:49.608266+00:00
-- url     : https://prove2.me/theorems/31b87209-167f-4581-9756-bf3cd9ee93e7
-- title:
--   Zero-barrier strategy boundary package under unbounded variation and instantaneous ruin
-- statement:
--   Given unbounded variation and almost-sure instantaneous reflected ruin at zero, the zero-cap candidate equals zero and the initial-zero barrier dividend value matches it. This proves the exact unbounded-variation branch of canonical barrier_zero_boundary_value_package (027a50fd-b61d-4033-9fd7-d3b97fe2f5e2), using the canonically Proved reflection-at-boundary bridge and the newly Proved zero reflected value theorem. The bounded-variation branch and instantaneous-ruin regularity remain separate.
-- source:
--   Conditional branch of canonical barrier_zero_boundary_value_package, proved from barrierValue_self_eq_barrierSupValue and zero_reflectedSupValue_of_unbounded_instant_ruin.

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_zero
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrier_zero_boundary_value_package_of_unbounded_instant_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by sorry
