-- Prove2me | Theorems.Thm_DenseTriangleFree_isPair_comp
-- name    : DenseTriangleFree.isPair_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:04.96048+00:00
-- url     : https://prove2.me/theorems/911fb827-e124-5412-854d-cce867ba63d7
-- title:
--   Dense Triangle Free: is Pair comp
-- statement:
--   The Dense Triangle Free construction uses the is Pair comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L50-L56
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/KeyLemma.lean#L50-L56

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

theorem DenseTriangleFree.isPair_comp {a : V} {U : Fin 5 → V} (hp : IsPair G a U) (r : Fin 5) (s : Bool) :
    IsPair G a (U ∘ sig r s) := by sorry
