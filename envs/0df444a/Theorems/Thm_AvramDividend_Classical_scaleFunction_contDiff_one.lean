-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T23:26:11.223455+00:00
-- url     : https://prove2.me/theorems/6b0b9766-0846-4796-8804-04d9518d2567
-- title:
--   The q-scale function is continuously differentiable on the positive half-line
-- statement:
--   Under the standing assumptions, condition (3.3) puts the spectrally negative Lévy process in a regime where, for q>0, its q-scale function is continuously differentiable on (0,∞). This stronger regularity statement supplies both differentiability of W and continuity of W' used later in Lemma 2(i) and Lemma 3(i).
-- source:
--   Avram, Palmowski, Pistorius, arXiv:math/0702893v1, condition (3.3) and the scale-function regularity stated after (3.4), p. 5; Chan, Kyprianou, Savov, arXiv:0903.1467, smoothness results for scale functions of spectrally negative Lévy processes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_one {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry

end AvramDividend.Classical
