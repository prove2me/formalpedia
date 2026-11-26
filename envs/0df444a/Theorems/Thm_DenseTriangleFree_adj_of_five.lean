-- Prove2me | Theorems.Thm_DenseTriangleFree_adj_of_five
-- name    : DenseTriangleFree.adj_of_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:34.961844+00:00
-- url     : https://prove2.me/theorems/366a3cd2-2bee-4d95-ae74-aebded8de86a
-- title:
--   Dense Triangle Free: adj of five
-- statement:
--   Every vertex sees some vertex of a closed walk of length 5, stated with explicit vertices.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L42-L48
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L42-L48

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

theorem DenseTriangleFree.adj_of_five
    (hZ : ∀ (a : V) (U : Fin 5 → V), (∀ i, G.Adj (U i) (U (i + 1))) → ∃ i, G.Adj a (U i))
    (a w0 w1 w2 w3 w4 : V) (e0 : G.Adj w0 w1) (e1 : G.Adj w1 w2) (e2 : G.Adj w2 w3)
    (e3 : G.Adj w3 w4) (e4 : G.Adj w4 w0) :
    G.Adj a w0 ∨ G.Adj a w1 ∨ G.Adj a w2 ∨ G.Adj a w3 ∨ G.Adj a w4 := by sorry
