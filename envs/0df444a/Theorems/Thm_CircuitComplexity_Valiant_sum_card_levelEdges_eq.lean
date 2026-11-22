-- Prove2me | Theorems.Thm_CircuitComplexity_Valiant_sum_card_levelEdges_eq
-- name    : CircuitComplexity.Valiant.sum_card_levelEdges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:03.511812+00:00
-- url     : https://prove2.me/theorems/6ac46080-c19c-4d6f-a533-74f53c6e3a76
-- title:
--   Valiant: sum card level Edges eq
-- statement:
--   **Partition.** When `G` is acyclic and `G.depth ≤ 2 ^ k`, every
--   edge lies in exactly one level `E_i` for `i ∈ {1,...,k}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L378-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L378-L383

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

theorem CircuitComplexity.Valiant.sum_card_levelEdges_eq
    (G : Digraph V) [DecidableRel G.Adj] {k : ℕ}
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k) :
    ∑ i ∈ Finset.Ioc 0 k, (levelEdges G k i).card = G.edgeFinset.card := by sorry
