-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_trace_mono
-- name    : DeciSigma1.Semantics.Tree.trace_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:46.723838+00:00
-- url     : https://prove2.me/theorems/75cf0ad4-a2c1-4200-8a2c-5dc9fb6e2b01
-- title:
--   Tree: trace mono
-- statement:
--   The Tree construction uses the trace mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L234-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L234-L238

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree

theorem DeciSigma1.Semantics.Tree.trace_mono {t u : Tree n} (h : t ≤ u) (ν : List (Fin n)) :
    trace t ν ≤ trace u ν := by sorry
