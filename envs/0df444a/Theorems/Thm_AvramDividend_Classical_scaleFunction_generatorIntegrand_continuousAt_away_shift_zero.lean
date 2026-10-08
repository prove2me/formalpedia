-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_continuousAt_away_shift_zero
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_continuousAt_away_shift_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:22:04.713113+00:00
-- url     : https://prove2.me/theorems/4fdb2d95-604f-475e-b7bd-cb26c8fdf99e
-- title:
--   State continuity of the compensated scale-function increment except at the origin-crossing jump
-- statement:
--   If a scale function is C2 near a positive state x, then for every jump y with x+y≠0 the generator's compensated increment is continuous as a function of the state at x. The only excluded jump is y=-x, where W may have a bounded-variation origin discontinuity. Follows from q-scale continuity away from zero, C2 derivative continuity near x, and fixed-jump generator increment continuity.
-- source:
--   The C2 compact branch of Avram Dividend Lemma 4 and the preceding fixed-jump continuity theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_continuousAt_away_shift_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x y : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hshift : x + y ≠ 0) :
    ContinuousAt
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y) x := by sorry

end AvramDividend.Classical
