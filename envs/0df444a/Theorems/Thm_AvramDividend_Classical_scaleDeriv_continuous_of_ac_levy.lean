-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_ac_levy
-- name    : AvramDividend.Classical.scaleDeriv_continuous_of_ac_levy
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T22:13:31.639124+00:00
-- url     : https://prove2.me/theorems/156517ba-b0cc-4337-a0c0-db8df13acd36
-- title:
--   Scale-function derivative continuity for an absolutely continuous Lévy measure
-- statement:
--   If the Lévy measure is absolutely continuous with respect to Lebesgue measure, then for q>0 the derivative of the q-scale function is continuous on (0,∞). This is the absolutely-continuous-measure branch of condition (3.3).
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, condition (3.3), p. 5, and the scale-function regularity used in Lemma 2(i), p. 15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_continuous_of_ac_levy {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hac : X.ν ≪ volume) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry

end AvramDividend.Classical
