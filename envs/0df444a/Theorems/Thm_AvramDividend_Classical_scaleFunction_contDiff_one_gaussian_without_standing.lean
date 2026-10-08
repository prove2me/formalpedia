-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_gaussian_without_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:34:44.411168+00:00
-- url     : https://prove2.me/theorems/6760cad5-19e6-4644-aef4-59a4ab200001
-- title:
--   Gaussian smoothing gives C1 q-scale-function regularity without auxiliary standing assumptions
-- statement:
--   A strictly positive Gaussian coefficient of a spectrally negative Levy process smooths the q-resolvent density, and its q-scale function W is continuously differentiable on the strictly positive axis. The paper's auxiliary Standing condition, which adds integrability of X1, is not mathematically needed for this Gaussian regularity branch. The statement is a common analytic strengthening needed by the existing C1 Gaussian and derivative-continuity Gaussian milestones, and it assumes the existing canonical Laplace-transform-defined IsScaleFunction without changing that definition.
-- source:
--   Chan, Kyprianou and Savov, Smoothness of scale functions for spectrally negative Levy processes (2011); Avram, Palmowski and Pistorius (2007) Condition (3.3), Section 3.1 and Lemma 2(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_one_gaussian_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry

end AvramDividend.Classical
