-- Prove2me | Theorems.Thm_DenseTriangleFree_normal_form
-- name    : DenseTriangleFree.normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:58.670883+00:00
-- url     : https://prove2.me/theorems/0bf4951a-bd3c-5df3-ac49-2f9ba91f02ef
-- title:
--   Dense Triangle Free: normal form
-- statement:
--   The Dense Triangle Free construction uses the normal form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L36-L46
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L36-L46

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.normal_form : ∀ S : Finset (Fin 5), ∃ r : Fin 5, ∃ s : Bool,
    (Finset.univ.filter fun i => sig r s i ∈ S).card = S.card ∧
    ((Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2, 3, 4} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2, 3} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 2} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1, 3} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 1} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0, 2} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = {0} ∨
     (Finset.univ.filter fun i => sig r s i ∈ S) = ∅) := by sorry
