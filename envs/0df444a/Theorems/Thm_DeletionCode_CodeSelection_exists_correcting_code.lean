-- Prove2me | Theorems.Thm_DeletionCode_CodeSelection_exists_correcting_code
-- name    : DeletionCode.CodeSelection.exists_correcting_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:28.176502+00:00
-- url     : https://prove2.me/theorems/95ac3349-f689-4144-8377-5f7f805c580f
-- title:
--   Code Selection: exists correcting code
-- statement:
--   From the actual graph and hash alone, retain at least one word for each
--   2Q good vertices, in multiplication form. No probability estimate enters
--   this deterministic selection step.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeSelection.lean#L60-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeSelection.lean#L60-L87

import Definitions.Def_DeletionCode_BipartiteSelection
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_CodeSelection
set_option autoImplicit true
open DeletionCode DeletionCode.CodeSelection
open HeaderRecovery ConflictGraphWitness BipartiteSelection
variable {n k : ℕ}

theorem DeletionCode.CodeSelection.exists_correcting_code (t Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) :
    ∃ C : Finset (Bits n),
      (goodVertices (graph (n := n) t Q H)).card ≤ 2 * Q * C.card ∧ Corrects t C := by sorry
