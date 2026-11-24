-- Prove2me | Theorems.Thm_Erdos1219_ofFinsetColouring_apply
-- name    : Erdos1219.ofFinsetColouring_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:39:51.919839+00:00
-- url     : https://prove2.me/theorems/748cc05c-d28b-4a10-9fcf-617267a713af
-- title:
--   Erdos1219: of Finset Colouring apply
-- statement:
--   The Erdos1219 construction uses the of Finset Colouring apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Defs.lean#L45-L51
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Defs.lean#L45-L51

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

theorem Erdos1219.ofFinsetColouring_apply [DecidableEq V] (col : {s : Finset V // s.card = 2} → Bool)
    {x y : V} (h : x ≠ y) :
    ofFinsetColouring col x y = col ⟨{x, y}, Finset.card_pair h⟩ := by sorry
