-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationSubgroup_orientationPreservingSigns_index
-- name    : BookProof.ChapterFreeFieldBornSignOrientationSubgroup.orientationPreservingSigns_index
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T03:59:34.748695+00:00
-- url     : https://prove2.me/theorems/3c119869-1c4d-410a-84f8-1410808f5433
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.orientationPreservingSigns_index` (n : ℕ) : (orientationPreservingSigns (n + 1)).index = 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationSubgroup`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.orientationPreservingSigns_index` (n : ℕ) : (orientationPreservingSigns (n + 1)).index = 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.orientationPreservingSigns_index`.

-- Generated from ChapterFreeFieldBornSignOrientationSubgroup.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationSubgroup.orientationPreservingSigns_index
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
import Definitions.Def_ChapterFreeFieldBornSignOrientationCard
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientationKernel
open BookProof.ChapterFreeFieldBornSignOrientationCard

theorem BookProof.ChapterFreeFieldBornSignOrientationSubgroup.orientationPreservingSigns_index (n : ℕ) :
    (orientationPreservingSigns (n + 1)).index = 2 := by sorry
