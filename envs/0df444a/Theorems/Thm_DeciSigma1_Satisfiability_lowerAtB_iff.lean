-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_lowerAtB_iff
-- name    : DeciSigma1.Satisfiability.lowerAtB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:55:52.991311+00:00
-- url     : https://prove2.me/theorems/432590f2-4139-416d-bb7b-11f6a058d047
-- title:
--   Satisfiability: lower At B iff
-- statement:
--   The Satisfiability construction uses the lower At B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L59-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L59-L61

module
public import Mathlib.Data.Finset.Lattice.Fold
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Satisfiability.lowerAtB_iff (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    lowerAtB Γ π x y = true ↔ LowerAt Γ π x y := by sorry
