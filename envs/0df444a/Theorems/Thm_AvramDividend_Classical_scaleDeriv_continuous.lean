-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
-- name    : AvramDividend.Classical.scaleDeriv_continuous
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T21:45:36.667991+00:00
-- url     : https://prove2.me/theorems/92e7c3df-0045-48c0-a0dd-d6c15d3cf225
-- title:
--   The scale-function derivative is continuous on (0,∞)
-- statement:
--   Under the standing assumptions and q>0, the derivative of the q-scale function is continuous on the positive half-line. Condition (3.3) is precisely the mission's regularity assumption: a Gaussian component, unbounded variation, or an absolutely continuous Lévy measure.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, condition (3.3), p. 5, and proof of Lemma 2(i), p. 15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_continuous {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry

end AvramDividend.Classical
