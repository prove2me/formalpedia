-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_exactStates_le_physicalStates
-- name    : BookProof.BrstReducedTransfer.exactStates_le_physicalStates
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:10:05.260094+00:00
-- url     : https://prove2.me/theorems/af2027b0-349d-48cc-b5db-e98aecb3a11c
-- title:
--   `BookProof.BrstReducedTransfer.exactStates_le_physicalStates` (hnil : ∀ x, Om (Om x) = 0) : exactStates Om ≤ physicalStates Om
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.exactStates_le_physicalStates` (hnil : ∀ x, Om (Om x) = 0) : exactStates Om ≤ physicalStates Om
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.exactStates_le_physicalStates`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.exactStates_le_physicalStates
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

theorem BookProof.BrstReducedTransfer.exactStates_le_physicalStates (hnil : ∀ x, Om (Om x) = 0) :
    exactStates Om ≤ physicalStates Om := by sorry
