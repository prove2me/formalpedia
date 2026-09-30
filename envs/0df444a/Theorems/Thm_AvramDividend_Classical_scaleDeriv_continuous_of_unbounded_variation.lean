-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_unbounded_variation
-- name    : AvramDividend.Classical.scaleDeriv_continuous_of_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T22:24:19.466336+00:00
-- url     : https://prove2.me/theorems/4b791ca2-c2e1-4982-8f32-2a0b2912836e
-- title:
--   Scale-function derivative continuity in the infinite small-jump variation case
-- statement:
--   If the small negative jumps have infinite total variation, then for q>0 the derivative of the q-scale function is continuous on (0,∞). This is the unbounded-variation branch of condition (3.3).
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, condition (3.3), p. 5, and the scale-function regularity used in Lemma 2(i), p. 15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_continuous_of_unbounded_variation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν = ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry

end AvramDividend.Classical
