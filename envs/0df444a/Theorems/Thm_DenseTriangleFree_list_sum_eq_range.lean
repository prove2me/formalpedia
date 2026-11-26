-- Prove2me | Theorems.Thm_DenseTriangleFree_list_sum_eq_range
-- name    : DenseTriangleFree.list_sum_eq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:16.323961+00:00
-- url     : https://prove2.me/theorems/a90e929e-15d1-48f3-b1d8-f9264c5f0dfe
-- title:
--   Dense Triangle Free: list sum eq range
-- statement:
--   The Dense Triangle Free construction uses the list sum eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L149-L153
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L149-L153

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.list_sum_eq_range (ws : List ℕ) : ws.sum = ∑ i ∈ Finset.range ws.length, ws.getD i 0 := by sorry
