-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_Script_trans
-- name    : DeletionCode.EditAlignment.Script.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:01:38.081609+00:00
-- url     : https://prove2.me/theorems/8c2aa2b0-a14c-46f8-9b64-731f35ff369d
-- title:
--   Script: trans
-- statement:
--   The Script construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L31-L37
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L31-L37

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.Script.trans {x y z : Word} {d₁ i₁ d₂ i₂ : ℕ}
    (hxy : Script x y d₁ i₁) (hyz : Script y z d₂ i₂) :
    Script x z (d₁ + d₂) (i₁ + i₂) := by sorry
