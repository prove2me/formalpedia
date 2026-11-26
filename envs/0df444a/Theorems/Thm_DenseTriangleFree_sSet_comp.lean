-- Prove2me | Theorems.Thm_DenseTriangleFree_sSet_comp
-- name    : DenseTriangleFree.sSet_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:31.69636+00:00
-- url     : https://prove2.me/theorems/0d88ece6-c86b-4487-9823-d5e0a0fb8e15
-- title:
--   Dense Triangle Free: s Set comp
-- statement:
--   The Dense Triangle Free construction uses the s Set comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L58-L65
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L58-L65

module
public import Mathlib
public import Definitions.Def_JinLib_Patterns
public import Definitions.Def_JinLib_KeyLemma
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

theorem DenseTriangleFree.sSet_comp (a : V) (U : Fin 5 → V) (r : Fin 5) (s : Bool) :
    sSet G a (U ∘ sig r s) = Finset.univ.filter fun i => sig r s i ∈ sSet G a U := by sorry
