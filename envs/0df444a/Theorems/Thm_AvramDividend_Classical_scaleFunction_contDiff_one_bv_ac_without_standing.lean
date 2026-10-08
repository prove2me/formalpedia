-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_bv_ac_without_standing
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_bv_ac_without_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:39:42.682983+00:00
-- url     : https://prove2.me/theorems/8b2fe922-4c54-40cd-b39d-c0b4de477ffb
-- title:
--   Bounded-variation absolutely continuous Lévy scale functions are C1 on the positive axis
-- statement:
--   If a spectrally negative Levy process has bounded variation and the Levy measure is absolutely continuous, then its q-scale function is continuously differentiable on the positive real line. The drift-renewal equation identifies the tilted scale-function derivative as a sum of convolution densities of the continuous negative-jump tail kernel, whose local uniform convergence supplies continuity. The process's separate Standing first moment assumption is not needed for this analytic branch, making this theorem a common reusable strengthened statement.
-- source:
--   Avram, Palmowski and Pistorius (2007), condition (3.3), and Chan, Kyprianou, Savov (2011), differentiability of q-scale functions for atom-free Lévy measures.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_one_bv_ac_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry

end AvramDividend.Classical
