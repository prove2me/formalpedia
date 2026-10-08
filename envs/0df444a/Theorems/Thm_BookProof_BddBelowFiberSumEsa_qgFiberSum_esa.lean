-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_qgFiberSum_esa
-- name    : BookProof.BddBelowFiberSumEsa.qgFiberSum_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T13:16:06.31663+00:00
-- url     : https://prove2.me/theorems/1fb7c5da-6dde-4b25-9819-5dd2c7e34853
-- title:
--   The Lean 4 theorem `qgFiberSum_esa` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgFiberSum_esa` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.qgFiberSum_esa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_contDiff_qgFiberV
open BookProof.BddBelowFiberSumEsa

variable {ι : Type*}



open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

theorem BookProof.BddBelowFiberSumEsa.qgFiberSum_esa {M alpha : ℝ} (halpha : 0 < alpha) {d : ℕ} (omega : Fin d → ℝ) :
    EssentiallySelfAdjointOn (fiberCore (Option (Fin d)))
      (fiberSumHam (qgFiberV M alpha omega) (contDiff_qgFiberV M alpha omega)) := by sorry
