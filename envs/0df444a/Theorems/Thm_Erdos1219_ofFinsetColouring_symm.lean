-- Prove2me | Theorems.Thm_Erdos1219_ofFinsetColouring_symm
-- name    : Erdos1219.ofFinsetColouring_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:39:54.390893+00:00
-- url     : https://prove2.me/theorems/2a104843-fb94-4468-9f1a-cf56a1e43c6d
-- title:
--   Erdos1219: of Finset Colouring symm
-- statement:
--   The Erdos1219 construction uses the of Finset Colouring symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Defs.lean#L53-L61
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Defs.lean#L53-L61

import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card
import Definitions.Def_Erdos1219_Defs
set_option autoImplicit false
open Cardinal
open Erdos1219
universe u
variable {V : Type u}

theorem Erdos1219.ofFinsetColouring_symm (col : {s : Finset V // s.card = 2} → Bool) (x y : V) :
    ofFinsetColouring col x y = ofFinsetColouring col y x := by sorry
