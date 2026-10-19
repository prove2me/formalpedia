-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianClassificationList_atomSet_restrict_atomSet_inc
-- name    : BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:15:03.346719+00:00
-- url     : https://prove2.me/theorems/91f96e95-1129-469a-b747-c644df870357
-- title:
--   `BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc` (mu : Measure α) [IsFiniteMeasure mu] : atomSet (mu.restrict (atomSet mu)) = atomSet mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianClassificationList`.
--
--   `BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc` (mu : Measure α) [IsFiniteMeasure mu] : atomSet (mu.restrict (atomSet mu)) = atomSet mu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc`.
--
--   Replaces the unuploadable node `BookProof_ChapterAbelianClassificationList_atomSet_restrict_atomSet`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterAbelianClassificationList.lean — theorem BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc
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

theorem BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc (mu : Measure α) [IsFiniteMeasure mu] :
    atomSet (mu.restrict (atomSet mu)) = atomSet mu := by sorry
