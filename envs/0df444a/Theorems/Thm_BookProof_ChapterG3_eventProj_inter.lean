-- Prove2me | Theorems.Thm_BookProof_ChapterG3_eventProj_inter
-- name    : BookProof.ChapterG3.eventProj_inter
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:34:40.662405+00:00
-- url     : https://prove2.me/theorems/2c64a9a2-d2c4-4288-bdb4-07ab56c45887
-- title:
--   `BookProof.ChapterG3.eventProj_inter` (A B : Set X) : eventProj (A ∩ B) = eventProj A * eventProj B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.eventProj_inter` (A B : Set X) : eventProj (A ∩ B) = eventProj A * eventProj B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.eventProj_inter`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.eventProj_inter
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ConservativeDiagonal
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.eventProj_inter (A B : Set X) :
    eventProj (A ∩ B) = eventProj A * eventProj B := by sorry
