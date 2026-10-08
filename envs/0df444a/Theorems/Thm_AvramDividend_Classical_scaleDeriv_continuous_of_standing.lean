-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_standing
-- name    : AvramDividend.Classical.scaleDeriv_continuous_of_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:49:52.126707+00:00
-- url     : https://prove2.me/theorems/db2a4988-7996-46e4-b3ac-d6c716ae3f08
-- title:
--   Continuity of the q-scale derivative under the classical standing assumptions
-- statement:
--   Under the standing assumptions, the q-scale function is continuously differentiable on the positive axis, and in particular its ordinary real derivative is continuous there. This serves as the directly reusable regularity interface for optimal barrier derivatives. It follows from first-order continuous differentiability supplied separately by the theorem scaleFunction_contDiff_one_of_standing, whose three analytic branches are reduced to Gaussian, infinite small-jump variation, or absolutely continuous Levy measure.
-- source:
--   Avram, Palmowski, Pistorius (2007), condition (3.3), regularity in Lemma 2; pinned Mathlib ContDiffOn.continuousOn_deriv_of_isOpen.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem scaleDeriv_continuous_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry
end AvramDividend.Classical
