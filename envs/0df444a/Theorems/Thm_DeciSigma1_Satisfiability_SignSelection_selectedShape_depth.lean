-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_depth
-- name    : DeciSigma1.Satisfiability.SignSelection.selectedShape_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:14.004605+00:00
-- url     : https://prove2.me/theorems/b4fbfbb0-332a-4760-8418-ba1c6613e6a4
-- title:
--   Sign Selection: selected Shape depth
-- statement:
--   Without a cycle clash in the signed translation, the selected symmetric solution has bounded
--   depth.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L493-L497
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L493-L497

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

theorem DeciSigma1.Satisfiability.SignSelection.selectedShape_depth {c : Fin n → Bool} {Γ : List (LitT n V)}
    (hc : ¬ CycleClash (signed c Γ)) (z : (V × Bool)) (π : List (Fin n))
    (hπ : ((selectedShape c Γ z).fn π).isSome) :
    π.length ≤ Fintype.card (V × Bool) * Fintype.card (V × Bool) + 1 := by sorry
