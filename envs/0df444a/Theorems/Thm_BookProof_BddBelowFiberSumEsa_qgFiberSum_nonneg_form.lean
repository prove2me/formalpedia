-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_qgFiberSum_nonneg_form
-- name    : BookProof.BddBelowFiberSumEsa.qgFiberSum_nonneg_form
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-03T13:16:04.88269+00:00
-- url     : https://prove2.me/theorems/ed8dcda8-2eba-41d5-b820-c2f738d29e6a
-- title:
--   The Lean 4 theorem `qgFiberSum_nonneg_form` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgFiberSum_nonneg_form` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.qgFiberSum_nonneg_form
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterWallEsaSemibounded
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_contDiff_qgFiberV
open BookProof.WallEsaSemibounded
open BookProof.BddBelowFiberSumEsa

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.qgFiberSum_nonneg_form {M alpha : ℝ} (halpha : 0 < alpha) {d : ℕ} (omega : Fin d → ℝ) :
    SemiboundedBelowOn (fiberCore (Option (Fin d)))
      (fiberSumHam (qgFiberV M alpha omega) (contDiff_qgFiberV M alpha omega)) 0 := by sorry
