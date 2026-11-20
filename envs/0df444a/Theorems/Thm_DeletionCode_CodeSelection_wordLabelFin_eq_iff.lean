-- Prove2me | Theorems.Thm_DeletionCode_CodeSelection_wordLabelFin_eq_iff
-- name    : DeletionCode.CodeSelection.wordLabelFin_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:01.673675+00:00
-- url     : https://prove2.me/theorems/d60d869e-abfe-4d55-9ce5-1435f50a7b39
-- title:
--   Code Selection: word Label Fin eq iff
-- statement:
--   The Code Selection construction uses the word Label Fin eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeSelection.lean#L42-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeSelection.lean#L42-L55

import Definitions.Def_DeletionCode_BipartiteSelection
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_CodeSelection
set_option autoImplicit true
open DeletionCode DeletionCode.CodeSelection
open HeaderRecovery ConflictGraphWitness BipartiteSelection
variable {n k : ℕ}

theorem DeletionCode.CodeSelection.wordLabelFin_eq_iff (Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (x y : Bits n) :
    wordLabelFin Q hQ H x = wordLabelFin Q hQ H y ↔ wordLabel Q H x = wordLabel Q H y := by sorry
