-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_tendsto_atTop
-- name    : AvramDividend.Classical.scaleDeriv_continuous_tendsto_atTop
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T20:20:15.41908+00:00
-- url     : https://prove2.me/theorems/abf08782-e61d-4879-bd4f-6fb0cb8c7b88
-- title:
--   The scale-function derivative is continuous on (0,∞) and tends to +∞
-- statement:
--   For q>0 under the standing assumptions, the q-scale-function derivative W' is continuous on the positive half-line and tends to +∞ as x→∞. This is the regularity/growth input used in Lemma 2(i) to show the derivative infimum is attained in the interior unless the right endpoint 0 already gives the lower bound.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, Lemma 2(i), p. 15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_continuous_tendsto_atTop {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) ∧
      Filter.Tendsto (deriv W) Filter.atTop Filter.atTop := by sorry

end AvramDividend.Classical
