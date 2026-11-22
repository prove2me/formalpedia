-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_cycleClashB_iff_bounded
-- name    : DeciSigma1.Satisfiability.cycleClashB_iff_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:54:18.599675+00:00
-- url     : https://prove2.me/theorems/acc3f692-6590-4e06-bc6a-f8cc345d3db0
-- title:
--   Satisfiability: cycle Clash B iff bounded
-- statement:
--   The Satisfiability construction uses the cycle Clash B iff bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L416-L426
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Decide.lean#L416-L426

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
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Satisfiability.cycleClashB_iff_bounded (Γ : List (LitT n V)) :
    cycleClashB Γ = true ↔ ∃ ρ x y,
      0 < ρ.length ∧ ρ.length ≤ Fintype.card V * Fintype.card V ∧
      LowerAt Γ ρ x x ∧ Derives Γ x y ∧ UpperAt Γ ρ y y := by sorry
