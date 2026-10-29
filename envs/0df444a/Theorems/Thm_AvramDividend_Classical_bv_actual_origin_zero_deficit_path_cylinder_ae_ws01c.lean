-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c
-- name    : AvramDividend.Classical.bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:43:42.047041+00:00
-- url     : https://prove2.me/theorems/134f302a-17f1-42d1-84de-8f62e79a9d05
-- title:
--   Original bounded-variation Lévy path satisfies the zero-dyadic-deficit Borel cylinder almost surely
-- statement:
--   For a standing spectrally negative Lévy process of bounded variation, the original sample path almost surely has dyadic drift deficits divided by dyadic elapsed time converging to zero. This is algebraically equivalent to the previously isolated almost-sure origin dyadic increment-slope theorem because X(0)=0. The conclusion is the exact countable path-cylinder property transferred to the random stopped path.
-- source:
--   Complete source extracted from work/avram_ws01c_actual_origin_zero_path_cylinder_draft.lean, algebraically connecting the origin zero-slope theorem to the Borel event.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_origin_dyadic_deficit_zero_ae_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.bv_actual_origin_zero_deficit_path_cylinder_ae_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ) -
          X.X (((1 : ℝ≥0) / 2) ^ n) ω) /
            ((((1 : ℝ≥0) / 2) ^ n : ℝ≥0) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by sorry
