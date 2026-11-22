-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_cycleClash_bounded_of_long_path
-- name    : DeciSigma1.Satisfiability.cycleClash_bounded_of_long_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:56:29.260126+00:00
-- url     : https://prove2.me/theorems/e6b65306-c542-4ae1-aba1-c80f45594dfb
-- title:
--   Satisfiability: cycle Clash bounded of long path
-- statement:
--   Lower and upper path judgments through a common variable along a path longer than the number
--   of variable pairs give a cycle clash of length between one and that number.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L222-L253
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L222-L253

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

theorem DeciSigma1.Satisfiability.cycleClash_bounded_of_long_path (π : List (Fin n)) (x y z : V)
    (hl : LowerAt Γ π x z) (hu : UpperAt Γ π z y)
      (hlen : Fintype.card V * Fintype.card V < π.length) :
    ∃ ρ x' y', 0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt Γ ρ x' x' ∧ Derives Γ x' y' ∧ UpperAt Γ ρ y' y' := by sorry
