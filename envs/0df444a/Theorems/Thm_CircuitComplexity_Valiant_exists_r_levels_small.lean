-- Prove2me | Theorems.Thm_CircuitComplexity_Valiant_exists_r_levels_small
-- name    : CircuitComplexity.Valiant.exists_r_levels_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:04.994798+00:00
-- url     : https://prove2.me/theorems/6c9eeb07-bed3-4646-be2f-96b3db0c1066
-- title:
--   Valiant: exists r levels small
-- statement:
--   **Averaging.** There is a choice of `r` levels whose total edge
--   count is at most `r * S / k` (equivalently, `k * total ≤ r * S`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L429-L441
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L429-L441

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

theorem CircuitComplexity.Valiant.exists_r_levels_small
    (G : Digraph V) [DecidableRel G.Adj] {k r : ℕ} (hrk : r ≤ k)
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k) :
    ∃ I : Finset ℕ, I ⊆ Finset.Ioc 0 k ∧ I.card = r ∧
      k * (∑ i ∈ I, (levelEdges G k i).card) ≤ r * G.edgeFinset.card := by sorry
