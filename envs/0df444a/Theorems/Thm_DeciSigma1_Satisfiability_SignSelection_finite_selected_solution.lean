-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_finite_selected_solution
-- name    : DeciSigma1.Satisfiability.SignSelection.finite_selected_solution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:29.20581+00:00
-- url     : https://prove2.me/theorems/967830d6-c7f0-47d3-aa19-1e01984dcd09
-- title:
--   Sign Selection: finite selected solution
-- statement:
--   If the signed translation has a finite solution, the decoded selected shape is a finite solution
--   of `Γ` with variance `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L511-L529
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L511-L529

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
open DeciSigma1 DeciSigma1.Satisfiability DeciSigma1.Satisfiability.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
omit [Fintype V]

theorem DeciSigma1.Satisfiability.SignSelection.finite_selected_solution [Finite V] {c : Fin n → Bool} {Γ : List (LitT n V)}
    (hs : ∃ σ : (V × Bool) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) (signed c Γ)) :
    ∃ σ : V → FTree n, Constraints.SatT c (FTree.toTree ∘ σ) Γ ∧
      FTree.toTree ∘ σ = decoded c (selectedShape c Γ) := by sorry
