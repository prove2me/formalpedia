-- Prove2me | Theorems.Thm_DenseTriangleFree_colorable_three_of_five
-- name    : DenseTriangleFree.colorable_three_of_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:35.80763+00:00
-- url     : https://prove2.me/theorems/b4311d9d-d6dc-4b42-8737-da9c363dcf20
-- title:
--   Dense Triangle Free: colorable three of five
-- statement:
--   Under the hypotheses of `no_odd_walk`, `G` is 3-colourable.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L156-L194
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L156-L194

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem DenseTriangleFree.colorable_three_of_five (h3 : G.CliqueFree 3)
    (hcn : ∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w)
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i)) :
    G.Colorable 3 := by sorry
