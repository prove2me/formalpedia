-- Prove2me | Theorems.Thm_DenseTriangleFree_wsumL_filter
-- name    : DenseTriangleFree.wsumL_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:58.867165+00:00
-- url     : https://prove2.me/theorems/731b37e3-a364-51a0-8211-ca5a41ecdc46
-- title:
--   Dense Triangle Free: wsum L filter
-- statement:
--   The Dense Triangle Free construction uses the wsum L filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L155-L167
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L155-L167

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.wsumL_filter (ws : List ℕ) (q : ℕ → Prop) [DecidablePred q] :
    wsumL ws (((List.range ws.length).filter fun i => 0 < ws.getD i 0).filter
      (fun i => decide (q i))) =
      ∑ i ∈ Finset.range ws.length, (if q i then ws.getD i 0 else 0) := by sorry
