-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_Script_reverse
-- name    : DeletionCode.EditAlignment.Script.reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:04:00.410721+00:00
-- url     : https://prove2.me/theorems/18c65e4a-b680-446d-9455-170c0228af92
-- title:
--   Script: reverse
-- statement:
--   The Script construction uses the reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L39-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L39-L50

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.Script.reverse {y z : Word} {d i : ℕ} (h : Script y z d i) :
    Script z y i d := by sorry
