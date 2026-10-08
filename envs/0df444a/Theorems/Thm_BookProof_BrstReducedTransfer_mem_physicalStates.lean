-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_mem_physicalStates
-- name    : BookProof.BrstReducedTransfer.mem_physicalStates
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:10:03.174414+00:00
-- url     : https://prove2.me/theorems/1e395b39-78d6-4506-a383-8686de1c5cad
-- title:
--   `BookProof.BrstReducedTransfer.mem_physicalStates` {x : H} : x ∈ physicalStates Om ↔ Om x = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.mem_physicalStates` {x : H} : x ∈ physicalStates Om ↔ Om x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.mem_physicalStates`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.mem_physicalStates
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

theorem BookProof.BrstReducedTransfer.mem_physicalStates {x : H} : x ∈ physicalStates Om ↔ Om x = 0 := by sorry
