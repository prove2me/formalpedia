-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_selectedShape_sat
-- name    : DeciSigma1.Satisfiability.SignSelection.selectedShape_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:08.637843+00:00
-- url     : https://prove2.me/theorems/e118537d-1788-41b2-bacc-16e86aea8f93
-- title:
--   Sign Selection: selected Shape sat
-- statement:
--   The Sign Selection construction uses the selected Shape sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L477-L479
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L477-L479

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

theorem DeciSigma1.Satisfiability.SignSelection.selectedShape_sat {c : Fin n → Bool} {Γ : List (LitT n V)}
    (hl : ¬ LabelClash (signed c Γ)) : Covariant.Sat (selectedShape c Γ) (signed c Γ) := by sorry
