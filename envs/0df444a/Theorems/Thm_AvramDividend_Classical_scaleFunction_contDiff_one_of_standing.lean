-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:45:33.934039+00:00
-- url     : https://prove2.me/theorems/310bb0bc-35b9-4c25-9b8e-14321f68ced1
-- title:
--   Scale-function C1 regularity under the classical dividend standing assumptions
-- statement:
--   Under the classical dividend paper's Standing assumptions, the q-scale function is continuously differentiable on the positive real line. Standing includes Condition (3.3), which covers the Gaussian, infinite small-jump variation and absolutely continuous Lévy-measure cases. This result packages the now separately formalised regularity branches for downstream optimal-barrier verification and scale-function derivative arguments.
-- source:
--   Avram, Palmowski and Pistorius (2007), standing assumptions and Condition (3.3), used in Lemmas 2–4 and Theorem 2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_one_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry

end AvramDividend.Classical
