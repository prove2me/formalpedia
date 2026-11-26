-- Prove2me | Theorems.Thm_DenseTriangleFree_sig_step
-- name    : DenseTriangleFree.sig_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:56.670056+00:00
-- url     : https://prove2.me/theorems/0d817f37-3af5-55db-9bf7-d5751a5eaff1
-- title:
--   Dense Triangle Free: sig step
-- statement:
--   The Dense Triangle Free construction uses the sig step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L29-L30
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L29-L30

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.sig_step : ∀ (r : Fin 5) (s : Bool) (i : Fin 5),
    sig r s (i + 1) = sig r s i + 1 ∨ sig r s i = sig r s (i + 1) + 1 := by sorry
