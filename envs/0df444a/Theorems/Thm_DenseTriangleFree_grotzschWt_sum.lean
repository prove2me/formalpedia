-- Prove2me | Theorems.Thm_DenseTriangleFree_grotzschWt_sum
-- name    : DenseTriangleFree.grotzschWt_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:07.727736+00:00
-- url     : https://prove2.me/theorems/9ff5af73-7a22-4fb7-889d-32124782ad7e
-- title:
--   Dense Triangle Free: grotzsch Wt sum
-- statement:
--   The Dense Triangle Free construction uses the grotzsch Wt sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L118-L118
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L118-L118

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree

theorem DenseTriangleFree.grotzschWt_sum : ∑ i, grotzschWt i = 29 := by sorry
