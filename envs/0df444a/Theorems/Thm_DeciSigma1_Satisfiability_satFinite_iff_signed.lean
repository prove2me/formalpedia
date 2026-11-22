-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_satFinite_iff_signed
-- name    : DeciSigma1.Satisfiability.satFinite_iff_signed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:52:42.376714+00:00
-- url     : https://prove2.me/theorems/60c2182e-098f-4dcd-80e1-40f376e9cd92
-- title:
--   Satisfiability: sat Finite iff signed
-- statement:
--   A constraint with variance has a finite solution exactly when its signed translation has one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L556-L571
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L556-L571

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
omit [Fintype V]

theorem DeciSigma1.Satisfiability.satFinite_iff_signed [Finite V] (c : Fin n → Bool) (Γ : List (LitT n V)) :
    (∃ σ : V → FTree n, SatT c (FTree.toTree ∘ σ) Γ) ↔
      (∃ σ : (V × Bool) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) (signed c Γ)) := by sorry
