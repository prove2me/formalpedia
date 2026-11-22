-- Prove2me | Theorems.Thm_CircuitComplexity_Valiant_canonicalLabel_le_depth
-- name    : CircuitComplexity.Valiant.canonicalLabel_le_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:16.104813+00:00
-- url     : https://prove2.me/theorems/018149ab-d6a9-4257-bb4b-8e99dd4932b7
-- title:
--   Valiant: canonical Label le depth
-- statement:
--   In an acyclic digraph, the canonical label is bounded above by the
--   graph's depth. (In a cyclic digraph the canonical label can exceed the
--   walk-supremum `depth = 0`, so acyclicity is needed.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L89-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L89-L96

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

theorem CircuitComplexity.Valiant.canonicalLabel_le_depth
    (G : Digraph V) (hac : IsAcyclic G) (v : V) :
    G.canonicalLabel v ≤ G.depth := by sorry
