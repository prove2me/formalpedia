-- Prove2me | Theorems.Thm_BookProof_ChapterG3_eventProj_comm
-- name    : BookProof.ChapterG3.eventProj_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:34:43.851616+00:00
-- url     : https://prove2.me/theorems/1f084b81-2a73-4f62-b3ef-5b0523b7bea9
-- title:
--   `BookProof.ChapterG3.eventProj_comm` (A B : Set X) : eventProj A * eventProj B = eventProj B * eventProj A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.eventProj_comm` (A B : Set X) : eventProj A * eventProj B = eventProj B * eventProj A
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.eventProj_comm`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.eventProj_comm
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ConservativeDiagonal
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.eventProj_comm (A B : Set X) :
    eventProj A * eventProj B = eventProj B * eventProj A := by sorry
