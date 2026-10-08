-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
-- name    : AvramDividend.Classical.scaleFunction_continuousAt_away_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:20:35.382212+00:00
-- url     : https://prove2.me/theorems/0dfe2e0c-ef19-4529-9ea0-e7db44c5b588
-- title:
--   A q-scale function is continuous at every nonzero real argument
-- statement:
--   The q-scale function is identically zero on (-∞,0) and is continuous on [0,∞). Hence it is continuous at every real point except possibly the origin. This is the missing source-level continuity input for a.e. fixed-jump continuity: at state x>0 the shifted point x+y fails this criterion only for y=-x.
-- source:
--   Definition of IsScaleFunction in the Avram Dividend mission; topology of eventually equal functions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_continuousAt_away_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (z : ℝ) (hz : z ≠ 0) :
    ContinuousAt W z := by sorry

end AvramDividend.Classical
