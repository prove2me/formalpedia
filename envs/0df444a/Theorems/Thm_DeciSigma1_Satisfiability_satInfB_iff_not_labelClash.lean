-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_satInfB_iff_not_labelClash
-- name    : DeciSigma1.Satisfiability.satInfB_iff_not_labelClash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:31.971753+00:00
-- url     : https://prove2.me/theorems/2cbf6ccb-fe12-4b3b-907d-b19e5493018e
-- title:
--   Satisfiability: sat Inf B iff not label Clash
-- statement:
--   The Satisfiability construction uses the sat Inf B iff not label Clash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L73-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L73-L75

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

theorem DeciSigma1.Satisfiability.satInfB_iff_not_labelClash (Γ : List (LitT n V)) :
    satInfB Γ = true ↔ ¬ LabelClash Γ := by sorry
