-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_condition33
-- name    : AvramDividend.Classical.scaleFunction_contDiff_one_of_condition33
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:44:58.721238+00:00
-- url     : https://prove2.me/theorems/caa61d14-3aac-46c9-b420-1960f802000a
-- title:
--   C1 regularity of q-scale functions from Avram condition (3.3)
-- statement:
--   Condition (3.3) has three source-faithful branches: nonzero Gaussian coefficient, infinite first absolute moment of small negative jumps, and absolutely continuous Lévy measure. The first two give C1 regularity of the scale function directly. In the absolutely continuous branch, if the process has unbounded variation then Gaussian or infinite jump variation applies, while in bounded variation the atom-free renewal-kernel representation gives C1 regularity. Thus W is C1 on (0,infinity) under Condition33 without assuming other Standing hypotheses. This target synthesises the three independent common analytic lemmas into the exact smoothness statement needed by the dividend verification work.
-- source:
--   Avram, Palmowski and Pistorius (2007), Condition (3.3), §3.1 and Lemma 2; Chan, Kyprianou, Savov (2011), scale-function smoothness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem scaleFunction_contDiff_one_of_condition33
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h33 : X.Condition33) :
    ContDiffOn ℝ 1 W (Ioi 0) := by sorry

end AvramDividend.Classical
