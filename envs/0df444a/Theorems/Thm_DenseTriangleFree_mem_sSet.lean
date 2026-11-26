-- Prove2me | Theorems.Thm_DenseTriangleFree_mem_sSet
-- name    : DenseTriangleFree.mem_sSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:07.994283+00:00
-- url     : https://prove2.me/theorems/47b52233-d13b-549a-afd5-1edbefe7f4af
-- title:
--   Dense Triangle Free: mem s Set
-- statement:
--   The Dense Triangle Free construction uses the mem s Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Pairs.lean#L38-L41
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Pairs.lean#L38-L41

module
public import Mathlib
public import Definitions.Def_JinLib_Heavy
public import Definitions.Def_JinLib_Pairs
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)

theorem DenseTriangleFree.mem_sSet {a : V} {U : Fin 5 → V} {i : Fin 5} :
    i ∈ sSet G a U ↔ ∃ t, G.Adj a t ∧ G.Adj (U (i - 1)) t ∧ G.Adj (U (i + 1)) t := by sorry
