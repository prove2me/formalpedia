-- Prove2me | Theorems.Thm_DenseTriangleFree_blowup_not_colorable
-- name    : DenseTriangleFree.blowup_not_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:49:10.819274+00:00
-- url     : https://prove2.me/theorems/bc2ca896-8527-5aaa-aaff-0ce8adf7d7e4
-- title:
--   Dense Triangle Free: blowup not colorable
-- statement:
--   The Dense Triangle Free construction uses the blowup not colorable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Blowup.lean#L63-L73
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Blowup.lean#L63-L73

module
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Blowup
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.blowup_not_colorable (m : ℕ) (hm : 0 < m) : ¬ (blowup m).Colorable 3 := by sorry
