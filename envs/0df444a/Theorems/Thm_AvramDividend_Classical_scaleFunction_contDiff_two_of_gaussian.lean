-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
-- name    : AvramDividend.Classical.scaleFunction_contDiff_two_of_gaussian
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T10:07:21.403998+00:00
-- url     : https://prove2.me/theorems/4c4d5e79-8440-49a7-a008-66422a4cd211
-- title:
--   Second-order scale-function smoothness from a positive Gaussian coefficient
-- statement:
--   For a spectrally negative Levy process with a strictly positive Gaussian coefficient, the q-scale function is C2 on the strictly positive half-line. This is the standard Brownian-smoothing regularity result required for the Gaussian branch of the generator calculation in Lemma 4.
-- source:
--   Avram, Palmowski and Pistorius (2007), smoothness discussion around equation (3.3) and the generator argument in Lemma 4; standard scale-function regularity for sigma>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_two_of_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 2 W (Ioi 0) := by sorry

end AvramDividend.Classical
