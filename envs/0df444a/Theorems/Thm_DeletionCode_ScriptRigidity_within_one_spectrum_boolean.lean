-- Prove2me | Theorems.Thm_DeletionCode_ScriptRigidity_within_one_spectrum_boolean
-- name    : DeletionCode.ScriptRigidity.within_one_spectrum_boolean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:53.104034+00:00
-- url     : https://prove2.me/theorems/c5f2c81c-d0fe-4760-b8fc-c3fae472455f
-- title:
--   Script Rigidity: within one spectrum boolean
-- statement:
--   The Script Rigidity construction uses the within one spectrum boolean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L45-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ScriptRigidity.lean#L45-L50

import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_ScriptRigidity
set_option autoImplicit true
open DeletionCode DeletionCode.ScriptRigidity
open Windows HeaderRecovery CatalogueWords EditAlignment SingleEditOrigins

theorem DeletionCode.ScriptRigidity.within_one_spectrum_boolean {k : ℕ} (hk : 1 ≤ k) (x y : List Bool)
    (hx : KUnique (listLetters x) x.length k) (hy : WithinEdits 1 x y) :
    ∀ g, SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 0 ∨
      SignedSupport.wordSpectrum (listLetters y) y.length (windowLength k) g = 1 := by sorry
