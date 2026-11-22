-- Prove2me | Theorems.Thm_CircuitComplexity_Valiant_depth_reduction
-- name    : CircuitComplexity.Valiant.depth_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:17.979064+00:00
-- url     : https://prove2.me/theorems/a3ce950d-691b-4a2d-8e3d-bd477eaf6cbc
-- title:
--   Valiant: depth reduction
-- statement:
--   **Valiant's Depth Reduction Lemma** (Valiant, 1977).
--
--   In any finite directed graph `G` with `S` edges and depth at most
--   `2 ^ k`, for any `r ≤ k`, there exists a set `F` of edges such
--   that:
--
--   * `F` is a subset of the edge set,
--   * `k * F.card ≤ r * S` (equivalent to `|F| ≤ r * S / k` without
--     integer division), and
--   * after removing `F`, the resulting digraph has depth at most
--     `2 ^ k / 2 ^ r`.
--
--   For cyclic `G` the hypothesis is satisfied trivially (with `depth = 0`)
--   and the conclusion holds with `F = ∅`. The substantive content is the
--   acyclic case, handled via Jukna's canonical labeling argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Valiant.lean#L64-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Valiant.lean#L64-L90

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Valiant
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph

theorem CircuitComplexity.Valiant.depth_reduction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj]
    {k r : Nat} (hrk : r ≤ k)
    (hd : G.depth ≤ 2 ^ k) :
    ∃ F : Finset (V × V),
      F ⊆ G.edgeFinset ∧
      k * F.card ≤ r * G.edgeFinset.card ∧
      (G.deleteEdges F).depth ≤ 2 ^ k / 2 ^ r := by sorry
