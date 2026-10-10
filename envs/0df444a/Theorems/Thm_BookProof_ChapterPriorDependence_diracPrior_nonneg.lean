-- Prove2me | Theorems.Thm_BookProof_ChapterPriorDependence_diracPrior_nonneg
-- name    : BookProof.ChapterPriorDependence.diracPrior_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:55:25.174203+00:00
-- url     : https://prove2.me/theorems/d4272d84-fa7f-48c9-b92c-c60a8b93d043
-- title:
--   `BookProof.ChapterPriorDependence.diracPrior_nonneg` (a x : Hyp) : 0 ≤ diracPrior a x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPriorDependence`.
--
--   `BookProof.ChapterPriorDependence.diracPrior_nonneg` (a x : Hyp) : 0 ≤ diracPrior a x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPriorDependence.diracPrior_nonneg`.

-- Generated from ChapterPriorDependence.lean — theorem BookProof.ChapterPriorDependence.diracPrior_nonneg
import Mathlib
import Definitions.Def_ChapterPriorDependence
open BookProof.ChapterPriorDependence


open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

theorem BookProof.ChapterPriorDependence.diracPrior_nonneg (a x : Hyp) : 0 ≤ diracPrior a x := by sorry
