-- Prove2me | Theorems.Thm_CircuitComplexity_Valiant_canonicalLabel_isLegal
-- name    : CircuitComplexity.Valiant.canonicalLabel_isLegal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:15.065366+00:00
-- url     : https://prove2.me/theorems/de2d37a0-e5a5-43c9-89d9-d3fa81bb1c79
-- title:
--   Valiant: canonical Label is Legal
-- statement:
--   **Canonical labeling is legal in acyclic graphs.** Any simple path
--   ending at `u` followed by the edge `(u,v)` is a strictly longer simple
--   path ending at `v` (using acyclicity to ensure `v` does not already
--   appear in the path).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L197-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/Valiant.lean#L197-L206

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

theorem CircuitComplexity.Valiant.canonicalLabel_isLegal (G : Digraph V) (hac : IsAcyclic G) :
    IsLegalLabeling G G.canonicalLabel := by sorry
