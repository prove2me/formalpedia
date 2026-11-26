-- Prove2me | Theorems.Thm_DenseTriangleFree_listsum_range
-- name    : DenseTriangleFree.listsum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:39.743801+00:00
-- url     : https://prove2.me/theorems/81082467-89c6-589c-a56e-0f8720e33f55
-- title:
--   Dense Triangle Free: listsum range
-- statement:
--   The Dense Triangle Free construction uses the listsum range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L135-L140
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L135-L140

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.listsum_range (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by sorry
