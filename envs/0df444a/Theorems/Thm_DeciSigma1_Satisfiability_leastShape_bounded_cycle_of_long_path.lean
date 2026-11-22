-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_bounded_cycle_of_long_path
-- name    : DeciSigma1.Satisfiability.leastShape_bounded_cycle_of_long_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:00.675888+00:00
-- url     : https://prove2.me/theorems/6e1014fb-2de7-42dc-b215-3cb2f2d11765
-- title:
--   Satisfiability: least Shape bounded cycle of long path
-- statement:
--   A path in the least shape longer than the number of variable pairs plus one gives
--   a cycle clash of length at most the number of pairs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L257-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L257-L272

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

theorem DeciSigma1.Satisfiability.leastShape_bounded_cycle_of_long_path {z : V} {π : List (Fin n)}
    (hdom : ((leastShape Γ z).fn π).isSome)
      (hlen : Fintype.card V * Fintype.card V + 1 < π.length) :
    ∃ ρ x y, 0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt Γ ρ x x ∧ Derives Γ x y ∧ UpperAt Γ ρ y y := by sorry
