-- Prove2me | Theorems.Thm_Digraph_deleteEdges_empty_depth
-- name    : Digraph.deleteEdges_empty_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:04.04473+00:00
-- url     : https://prove2.me/theorems/5de7e782-14e2-492b-a149-39424204d6f0
-- title:
--   Digraph: delete Edges empty depth
-- statement:
--   The directed-walk set of `G.deleteEdges ∅` agrees with that of `G`,
--   so the two graphs have the same depth.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Digraph/Defs.lean#L75-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Digraph/Defs.lean#L75-L81

module
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
set_option autoImplicit true
@[expose] public section
public section
open Digraph
variable {V : Type*}

theorem Digraph.deleteEdges_empty_depth (G : Digraph V) :
    (G.deleteEdges ∅).depth = G.depth := by sorry
