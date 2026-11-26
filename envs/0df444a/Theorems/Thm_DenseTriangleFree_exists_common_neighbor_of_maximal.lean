-- Prove2me | Theorems.Thm_DenseTriangleFree_exists_common_neighbor_of_maximal
-- name    : DenseTriangleFree.exists_common_neighbor_of_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:49:04.175031+00:00
-- url     : https://prove2.me/theorems/34380bd3-93cb-4882-bcf9-a2a6a379848f
-- title:
--   Dense Triangle Free: exists common neighbor of maximal
-- statement:
--   In a maximal triangle-free graph, two distinct non-adjacent vertices have a common
--   neighbour.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Maximal.lean#L37-L69
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Maximal.lean#L37-L69

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Maximal
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*}

theorem DenseTriangleFree.exists_common_neighbor_of_maximal {G : SimpleGraph V}
    (hG : Maximal (fun H : SimpleGraph V => H.CliqueFree 3) G) {u v : V} (huv : u ≠ v)
    (hnadj : ¬ G.Adj u v) : ∃ w, G.Adj u w ∧ G.Adj v w := by sorry
