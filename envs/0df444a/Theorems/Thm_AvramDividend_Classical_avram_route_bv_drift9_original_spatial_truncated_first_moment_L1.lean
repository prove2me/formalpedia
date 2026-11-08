-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
-- name    : AvramDividend.Classical.avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:07:52.455023+00:00
-- url     : https://prove2.me/theorems/11577b30-b5c4-4dec-a083-157def6124fc
-- title:
--   Original BV negative-jump truncated spatial first moment is integrable
-- statement:
--   For any positive spatial width epsilon at most one, the integrable first-order Lévy weight min(1, abs(z)) for the original bounded-variation process dominates min(epsilon, -z) on the negative jump half-line. Both weights are nonnegative and measurable there, so integrability follows by domination. This certificate supplies the real-valued Tonelli majorant for the original spatial HJB jump loss.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn (fun z : ℝ => min ε (-z)) (Iio (0 : ℝ)) X.ν := by sorry
