-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_SignSelection_decoded_selectedShape_sat
-- name    : DeciSigma1.Satisfiability.SignSelection.decoded_selectedShape_sat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:30.543562+00:00
-- url     : https://prove2.me/theorems/78187ebb-b00b-468b-bd08-a4e4ec7305cc
-- title:
--   Sign Selection: decoded selected Shape sat
-- statement:
--   If the signed translation has no label clash, the decoded selected shape solves `Γ` with
--   variance `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L502-L506
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L502-L506

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

theorem DeciSigma1.Satisfiability.SignSelection.decoded_selectedShape_sat {c : Fin n → Bool} {Γ : List (LitT n V)}
    (hl : ¬ LabelClash (signed c Γ)) : Constraints.SatT c (decoded c (selectedShape c Γ)) Γ := by sorry
