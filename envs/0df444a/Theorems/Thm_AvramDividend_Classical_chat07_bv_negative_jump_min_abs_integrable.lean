-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
-- name    : AvramDividend.Classical.chat07_bv_negative_jump_min_abs_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:26:30.329991+00:00
-- url     : https://prove2.me/theorems/fed15c2a-8b43-4ea5-9560-82e551f5d52f
-- title:
--   Finite first-order negative-jump weight for bounded-variation Lévy processes
-- statement:
--   For a spectrally negative Lévy process with bounded variation, the function y ↦ min(1,|y|) is integrable with respect to the Lévy jump measure on negative jumps. Pull back the proved finite truncated first moment of the positive jump-magnitude pushforward measure, using the pointwise equality |y| = -y on the negative half-line. This provides the first-order dominator for bounded-variation generator jump terms; it does not assume generator harmonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_bv_negative_jump_min_abs_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => min 1 |y|) (Iio 0) X.ν := by sorry
