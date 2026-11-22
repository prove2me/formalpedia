-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_domain
-- name    : DeciSigma1.Satisfiability.SignSelection.selectedShape_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:51:57.565647+00:00
-- url     : https://prove2.me/theorems/b31fc0b6-e2aa-4ebb-8904-1341c3062083
-- title:
--   Sign Selection: selected Shape domain
-- statement:
--   The Sign Selection construction uses the selected Shape domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L486-L489
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L486-L489

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

theorem DeciSigma1.Satisfiability.SignSelection.selectedShape_domain (c : Fin n → Bool) (Γ : List (LitT n V))
    (z : (V × Bool)) (π : List (Fin n)) :
    ((selectedShape c Γ z).fn π).isSome = ((leastShape (signed c Γ) z).fn π).isSome := by sorry
