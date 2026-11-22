-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_dual_eq_top
-- name    : DeciSigma1.Constraints.dual_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:06.098368+00:00
-- url     : https://prove2.me/theorems/450fdf5c-71b7-42ca-bb2e-bc46a55fc2ab
-- title:
--   Constraints: dual eq top
-- statement:
--   The Constraints construction uses the dual eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L84-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L84-L87

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.dual_eq_top (t : Semantics.Tree n) : Tree.dual t = Tree.top ↔ t = Tree.bot := by sorry
