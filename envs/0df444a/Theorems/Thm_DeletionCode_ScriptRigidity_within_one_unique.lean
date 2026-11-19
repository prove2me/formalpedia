-- Prove2me | Theorems.Thm_DeletionCode_ScriptRigidity_within_one_unique
-- name    : DeletionCode.ScriptRigidity.within_one_unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:20:17.440199+00:00
-- url     : https://prove2.me/theorems/60e65ac3-35c9-48c3-96ac-5b40156daf5c
-- title:
--   Script Rigidity: within one unique
-- statement:
--   Every actual word within one edit of a k-unique word is (L-1)-unique.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L39-L43
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L39-L43

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.ScriptRigidity.within_one_unique {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    KUnique (listLetters y) y.length (windowLength k - 1) := by sorry
