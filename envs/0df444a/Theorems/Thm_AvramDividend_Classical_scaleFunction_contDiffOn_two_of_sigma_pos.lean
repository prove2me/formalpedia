-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_two_of_sigma_pos
-- name    : AvramDividend.Classical.scaleFunction_contDiffOn_two_of_sigma_pos
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:13:56.669016+00:00
-- url     : https://prove2.me/theorems/f596d402-a449-4fb9-9bc5-65612928538b
-- title:
--   Gaussian q-scale functions are C2 away from zero
-- statement:
--   Regularity theorem used in Lemma 4. If the spectrally negative Lévy process has a Gaussian component σ>0 and satisfies the standing assumptions, then its q-scale function W is C² on (0,∞). This is the scale-function regularity fact cited by the source before applying Itô's formula.
-- source:
--   Avram, Palmowski and Pistorius (2007), discussion of scale-function smoothness around p. 14 and Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_contDiffOn_two_of_sigma_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ) :
    ContDiffOn ℝ 2 W (Ioi 0) := by sorry

end AvramDividend.Classical
