-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_leastShape_depth
-- name    : DeciSigma1.Satisfiability.leastShape_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:11.469835+00:00
-- url     : https://prove2.me/theorems/abeac509-0d6b-45f2-8ad8-2349c014a142
-- title:
--   Satisfiability: least Shape depth
-- statement:
--   Without a cycle clash, the least shape has depth at most the number of variable pairs plus
--   one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L276-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L276-L281

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

theorem DeciSigma1.Satisfiability.leastShape_depth (hn : ¬ CycleClash Γ) (z : V) (π : List (Fin n))
    (hdom : ((leastShape Γ z).fn π).isSome) : π.length ≤ Fintype.card V * Fintype.card V + 1 := by sorry
