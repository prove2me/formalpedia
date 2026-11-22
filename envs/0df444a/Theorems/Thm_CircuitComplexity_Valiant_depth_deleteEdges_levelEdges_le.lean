-- Prove2me | Theorems.Thm_CircuitComplexity_Valiant_depth_deleteEdges_levelEdges_le
-- name    : CircuitComplexity.Valiant.depth_deleteEdges_levelEdges_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:07.226647+00:00
-- url     : https://prove2.me/theorems/66c5cf55-ec54-4424-839c-1da00476ae03
-- title:
--   Valiant: depth delete Edges level Edges le
-- statement:
--   **Relabeling after removal.** After removing the edges in levels
--   `I` (assuming `G` acyclic), the map sending each vertex to its
--   canonical label with the `I`-th bits deleted is a legal labeling of
--   the remaining graph; its image has at most `2 ^ (k - I.card)` values,
--   so the remaining depth is bounded by that.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L603-L633
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L603-L633

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
variable [DecidableEq V]

theorem CircuitComplexity.Valiant.depth_deleteEdges_levelEdges_le
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k)
    (I : Finset ℕ) (hI : I ⊆ Finset.Ioc 0 k) :
    (G.deleteEdges (I.biUnion fun i => levelEdges G k i)).depth
      ≤ 2 ^ (k - I.card) := by sorry
