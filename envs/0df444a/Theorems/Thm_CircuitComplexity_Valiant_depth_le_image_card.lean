-- Prove2me | Theorems.Thm_CircuitComplexity_Valiant_depth_le_image_card
-- name    : CircuitComplexity.Valiant.depth_le_image_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:14.931685+00:00
-- url     : https://prove2.me/theorems/8f968345-b52a-4663-9292-a369ca3c3772
-- title:
--   Valiant: depth le image card
-- statement:
--   **Depth bound from a legal labeling.** Along any directed path,
--   labels are strictly increasing, hence distinct. So `depth(G)` is at
--   most the number of distinct labels used by any legal labeling.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L254-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L254-L273

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

theorem CircuitComplexity.Valiant.depth_le_image_card (G : Digraph V)
    {ℓ : V → ℕ} (hℓ : IsLegalLabeling G ℓ) :
    G.depth ≤ (Finset.univ.image ℓ).card := by sorry
