-- Prove2me | Theorems.Thm_DenseTriangleFree_sig_nbrs
-- name    : DenseTriangleFree.sig_nbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:54.010389+00:00
-- url     : https://prove2.me/theorems/0ecbe6b9-e607-5ec9-9c9a-06aed57d7231
-- title:
--   Dense Triangle Free: sig nbrs
-- statement:
--   The Dense Triangle Free construction uses the sig nbrs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L32-L34
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L32-L34

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.sig_nbrs : ∀ (r : Fin 5) (s : Bool) (i : Fin 5),
    (sig r s (i - 1) = sig r s i - 1 ∧ sig r s (i + 1) = sig r s i + 1) ∨
      (sig r s (i - 1) = sig r s i + 1 ∧ sig r s (i + 1) = sig r s i - 1) := by sorry
