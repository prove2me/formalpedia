-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianClassificationList_restrict_atomSet_pure_inc
-- name    : BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:15:13.706503+00:00
-- url     : https://prove2.me/theorems/48655623-e2d2-4025-aced-e4f172d8335f
-- title:
--   `BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc` (mu : Measure α) [IsFiniteMeasure mu] : (mu.restrict (atomSet mu)) (atomSet (mu.restrict (atomSet mu)))ᶜ = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianClassificationList`.
--
--   `BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc` (mu : Measure α) [IsFiniteMeasure mu] : (mu.restrict (atomSet mu)) (atomSet (mu.restrict (atomSet mu)))ᶜ = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc`.
--
--   Replaces the unuploadable node `BookProof_ChapterAbelianClassificationList_restrict_atomSet_pure`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterAbelianClassificationList.lean — theorem BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLpRestrictSplit
import Definitions.Def_ChapterLpScaleMeasure
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
open BookProof.ChapterAbelianClassificationList


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc (mu : Measure α) [IsFiniteMeasure mu] :
    (mu.restrict (atomSet mu)) (atomSet (mu.restrict (atomSet mu)))ᶜ = 0 := by sorry
