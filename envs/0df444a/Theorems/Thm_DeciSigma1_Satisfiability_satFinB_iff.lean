-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_satFinB_iff
-- name    : DeciSigma1.Satisfiability.satFinB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:59.153123+00:00
-- url     : https://prove2.me/theorems/77479cef-764e-4f7c-bd4a-fc8117c651c1
-- title:
--   Satisfiability: sat Fin B iff
-- statement:
--   `satFinB c` decides whether a constraint has a finite solution with variance `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L580-L582
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L580-L582

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
open DeciSigma1.Constraints DeciSigma1.Satisfiability.Covariant DeciSigma1.Semantics
open DeciSigma1.Semantics.SignSelection
variable {n : ℕ} {V : Type*} [Fintype V]
variable [DecidableEq V]

theorem DeciSigma1.Satisfiability.satFinB_iff (c : Fin n → Bool) (Γ : List (LitT n V)) :
    satFinB c Γ = true ↔ ∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) Γ := by sorry
