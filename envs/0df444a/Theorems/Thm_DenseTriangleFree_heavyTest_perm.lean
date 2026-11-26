-- Prove2me | Theorems.Thm_DenseTriangleFree_heavyTest_perm
-- name    : DenseTriangleFree.heavyTest_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:47.464819+00:00
-- url     : https://prove2.me/theorems/25a32a06-d659-462d-ad97-463ddf754998
-- title:
--   Dense Triangle Free: heavy Test perm
-- statement:
--   The Dense Triangle Free construction uses the heavy Test perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L78-L86
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L78-L86

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.heavyTest_perm (ws : List ℕ) (Fb Js : List (List ℕ)) (l l' : List ℕ) (h : l.Perm l') :
    heavyTest ws Fb Js l = heavyTest ws Fb Js l' := by sorry
