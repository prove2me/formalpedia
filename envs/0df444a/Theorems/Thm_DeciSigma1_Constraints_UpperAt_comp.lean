-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_UpperAt_comp
-- name    : DeciSigma1.Constraints.UpperAt.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:21:38.787224+00:00
-- url     : https://prove2.me/theorems/bc11b3b5-24a3-488a-8011-735493a9c28b
-- title:
--   Upper At: comp
-- statement:
--   The Upper At construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L447-L452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Closure.lean#L447-L452

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Constraints.UpperAt.comp {π π' : List (Fin n)} {z w y : V}
    (h : UpperAt Γ π z w) (h' : UpperAt Γ π' w y) :
    UpperAt Γ (π ++ π') z y := by sorry
