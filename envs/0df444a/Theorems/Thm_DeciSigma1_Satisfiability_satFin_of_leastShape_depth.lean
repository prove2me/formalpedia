-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_satFin_of_leastShape_depth
-- name    : DeciSigma1.Satisfiability.satFin_of_leastShape_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:11.979682+00:00
-- url     : https://prove2.me/theorems/4342f858-a539-4648-916d-416678d6fc32
-- title:
--   Satisfiability: sat Fin of least Shape depth
-- statement:
--   If the least shape has bounded depth, it truncates to a finite solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L359-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L359-L366

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

theorem DeciSigma1.Satisfiability.satFin_of_leastShape_depth (hn : ¬ LabelClash Γ)
    (hd : ∀ z π, ((leastShape Γ z).fn π).isSome → π.length ≤ Fintype.card V * Fintype.card V + 1) :
    ∃ σ : V → FTree n, Covariant.Sat (FTree.toTree ∘ σ) Γ := by sorry
