-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_treeLe_antisymm
-- name    : DeciSigma1.Semantics.treeLe_antisymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:16.722612+00:00
-- url     : https://prove2.me/theorems/1cf4faf5-8b49-4d14-acc2-89a4ee6efd3e
-- title:
--   Semantics: tree Le antisymm
-- statement:
--   The Semantics construction uses the tree Le antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L386-L389
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L386-L389

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

theorem DeciSigma1.Semantics.treeLe_antisymm {c : Fin n → Bool} {t u : Tree n}
    (htu : Le c t u) (hut : Le c u t) : t = u := by sorry
