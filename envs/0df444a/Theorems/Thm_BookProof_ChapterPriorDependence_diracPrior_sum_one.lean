-- Prove2me | Theorems.Thm_BookProof_ChapterPriorDependence_diracPrior_sum_one
-- name    : BookProof.ChapterPriorDependence.diracPrior_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:55:33.506413+00:00
-- url     : https://prove2.me/theorems/39fd8876-475a-4dd4-9732-75dd2c7af614
-- title:
--   `BookProof.ChapterPriorDependence.diracPrior_sum_one` (a : Hyp) : ∑ x, diracPrior a x = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPriorDependence`.
--
--   `BookProof.ChapterPriorDependence.diracPrior_sum_one` (a : Hyp) : ∑ x, diracPrior a x = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPriorDependence.diracPrior_sum_one`.

-- Generated from ChapterPriorDependence.lean — theorem BookProof.ChapterPriorDependence.diracPrior_sum_one
import Mathlib
import Definitions.Def_ChapterPriorDependence
open BookProof.ChapterPriorDependence


open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable [Fintype Hyp]

theorem BookProof.ChapterPriorDependence.diracPrior_sum_one (a : Hyp) : ∑ x, diracPrior a x = 1 := by sorry
