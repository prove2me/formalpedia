-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
-- name    : AvramDividend.Classical.scaleDeriv_continuous_of_gaussian
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T22:33:13.73228+00:00
-- url     : https://prove2.me/theorems/0e3c20a9-fc04-4a12-94b6-0b9ddcaa49b6
-- title:
--   Scale-function derivative continuity with a Gaussian component
-- statement:
--   If the spectrally negative Lévy process has a non-zero Gaussian component, then for q>0 the derivative of its q-scale function is continuous on (0,∞). This is the Gaussian branch of condition (3.3).
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, condition (3.3), p. 5, and the scale-function regularity used in Lemma 2(i), p. 15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_continuous_of_gaussian {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry

end AvramDividend.Classical
