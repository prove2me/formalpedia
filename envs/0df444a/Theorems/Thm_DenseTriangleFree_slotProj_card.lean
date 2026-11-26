-- Prove2me | Theorems.Thm_DenseTriangleFree_slotProj_card
-- name    : DenseTriangleFree.slotProj_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:21.73692+00:00
-- url     : https://prove2.me/theorems/7086f226-3f29-4130-947e-0fd8cdd1b20c
-- title:
--   Dense Triangle Free: slot Proj card
-- statement:
--   The Dense Triangle Free construction uses the slot Proj card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Blowup.lean#L26-L28
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Blowup.lean#L26-L28

module
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Blowup
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.slotProj_card : ∀ x : Fin 11,
    (Finset.univ.filter fun k : Fin 29 => grotzsch.Adj x (slotProj k)).card = 10 := by sorry
