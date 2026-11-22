-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_treeLe_false_iff_le
-- name    : DeciSigma1.Semantics.treeLe_false_iff_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:59.076012+00:00
-- url     : https://prove2.me/theorems/c502e029-1c6e-4f97-8a6f-975eb881c481
-- title:
--   Semantics: tree Le false iff le
-- statement:
--   The Semantics construction uses the tree Le false iff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L380-L381
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L380-L381

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.treeLe_false_iff_le (t u : Tree n) :
    Le (fun _ => false) t u ↔ t ≤ u := by sorry
