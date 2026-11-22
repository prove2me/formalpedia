-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_cycleClash_iff_bounded
-- name    : DeciSigma1.Satisfiability.cycleClash_iff_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:56:43.778505+00:00
-- url     : https://prove2.me/theorems/ca04a8b9-4639-4533-9de0-8a9a6e4ef581
-- title:
--   Satisfiability: cycle Clash iff bounded
-- statement:
--   Without a label clash, every cycle clash has a witness along a path of length between one and
--   the number of variable pairs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L385-L397
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L385-L397

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

theorem DeciSigma1.Satisfiability.cycleClash_iff_bounded (hn : ¬ LabelClash Γ) :
    CycleClash Γ ↔ ∃ ρ x y, 0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt Γ ρ x x ∧ Derives Γ x y ∧ UpperAt Γ ρ y y := by sorry
