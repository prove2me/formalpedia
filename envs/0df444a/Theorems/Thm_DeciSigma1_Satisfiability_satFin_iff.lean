-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_satFin_iff
-- name    : DeciSigma1.Satisfiability.satFin_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:52:03.240452+00:00
-- url     : https://prove2.me/theorems/e501d3c4-ff25-477b-b155-9de2d531919d
-- title:
--   Satisfiability: sat Fin iff
-- statement:
--   A covariant constraint has a finite solution exactly when it has neither a label clash nor a
--   cycle clash.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L371-L381
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L371-L381

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
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
omit [Fintype V]

theorem DeciSigma1.Satisfiability.satFin_iff [Finite V] : (∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ) ↔
    ¬ LabelClash Γ ∧ ¬ CycleClash Γ := by sorry
