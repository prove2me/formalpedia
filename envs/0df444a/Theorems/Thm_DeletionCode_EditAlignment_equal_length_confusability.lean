-- Prove2me | Theorems.Thm_DeletionCode_EditAlignment_equal_length_confusability
-- name    : DeletionCode.EditAlignment.equal_length_confusability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:04:20.435686+00:00
-- url     : https://prove2.me/theorems/358591d5-6da8-4151-96db-8ec3b0c02b06
-- title:
--   Edit Alignment: equal length confusability
-- statement:
--   Manuscript lemma `lem:confuse`. Distinctness is unnecessary for this conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L128-L139
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditAlignment.lean#L128-L139

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment

theorem DeletionCode.EditAlignment.equal_length_confusability (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ d, d ≤ t ∧ Alignment y z d d := by sorry
