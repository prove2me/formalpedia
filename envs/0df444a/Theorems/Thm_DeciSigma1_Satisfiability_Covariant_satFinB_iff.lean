-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_Covariant_satFinB_iff
-- name    : DeciSigma1.Satisfiability.Covariant.satFinB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:52:17.47428+00:00
-- url     : https://prove2.me/theorems/bd555f0c-e2f4-4531-be73-f5bd19ea1a17
-- title:
--   Covariant: sat Fin B iff
-- statement:
--   `Covariant.satFinB` decides whether a covariant constraint has a finite solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L456-L458
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L456-L458

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

theorem DeciSigma1.Satisfiability.Covariant.satFinB_iff (Γ : List (LitT n V)) :
    satFinB Γ = true ↔ ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by sorry
