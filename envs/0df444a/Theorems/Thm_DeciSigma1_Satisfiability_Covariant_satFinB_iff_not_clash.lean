-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_Covariant_satFinB_iff_not_clash
-- name    : DeciSigma1.Satisfiability.Covariant.satFinB_iff_not_clash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:56:58.272804+00:00
-- url     : https://prove2.me/theorems/891d7ea5-a4a3-450a-acf0-8e2c58d2b43c
-- title:
--   Covariant: sat Fin B iff not clash
-- statement:
--   The Covariant construction uses the sat Fin B iff not clash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L442-L453
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L442-L453

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
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Satisfiability.Covariant.satFinB_iff_not_clash (Γ : List (LitT n V)) :
    satFinB Γ = true ↔ ¬ LabelClash Γ ∧ ¬ CycleClash Γ := by sorry
