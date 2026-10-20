-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_scale_zero_extension_continuous_at_zero
-- name    : AvramDividend.Classical.chat03_scale_zero_extension_continuous_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:54:56.91763+00:00
-- url     : https://prove2.me/theorems/4cf60694-dfaf-4e15-a3d5-16fa35282b78
-- title:
--   Global zero-extension continuity at the origin when the scale function vanishes at zero
-- statement:
--   For the official q-scale function, if W(0)=0 then its negative-half-line zero extension agrees continuously with its nonnegative-half-line continuity at the origin. Consequently W is continuous at zero as a function on all real reserves. This is useful in the zero-reserve pathwise limit, provided W(0)=0 can be proved from other standing assumptions.
-- source:
--   Official IsScaleFunction zero-left and continuousOn nonnegative branch, glued using pinned Mathlib continuousOn union of two closed half-lines.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn

open MeasureTheory Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_scale_zero_extension_continuous_at_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) :
    ContinuousAt W 0 := by sorry
