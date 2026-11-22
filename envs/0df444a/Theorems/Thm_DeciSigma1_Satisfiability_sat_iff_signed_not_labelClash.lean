-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_sat_iff_signed_not_labelClash
-- name    : DeciSigma1.Satisfiability.sat_iff_signed_not_labelClash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:16.907788+00:00
-- url     : https://prove2.me/theorems/e5e9047f-07ff-4989-af91-ebecb40787ca
-- title:
--   Satisfiability: sat iff signed not label Clash
-- statement:
--   A constraint with variance is satisfiable exactly when its signed translation has no label
--   clash.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L544-L550
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L544-L550

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

theorem DeciSigma1.Satisfiability.sat_iff_signed_not_labelClash (c : Fin n → Bool) (Γ : List (LitT n V)) :
    (∃ ρ, SatT c ρ Γ) ↔ ¬ LabelClash (signed c Γ) := by sorry
