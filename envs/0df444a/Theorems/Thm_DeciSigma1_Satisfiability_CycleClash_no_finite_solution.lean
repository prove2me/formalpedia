-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_CycleClash_no_finite_solution
-- name    : DeciSigma1.Satisfiability.CycleClash.no_finite_solution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:59.113561+00:00
-- url     : https://prove2.me/theorems/dc0c8338-940e-4aff-b1e5-6009d8ac7eff
-- title:
--   Cycle Clash: no finite solution
-- statement:
--   A constraint with a cycle clash has no finite solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L198-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L198-L208

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
open DeciSigma1.Constraints DeciSigma1.Constraints.PathBounds DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] {Γ : List (LitT n V)}
omit [Fintype V]

theorem DeciSigma1.Satisfiability.CycleClash.no_finite_solution (hc : CycleClash Γ) :
    ¬ ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by sorry
