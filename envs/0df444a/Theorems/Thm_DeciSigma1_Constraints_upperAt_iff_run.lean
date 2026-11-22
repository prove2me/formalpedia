-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_upperAt_iff_run
-- name    : DeciSigma1.Constraints.upperAt_iff_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:24:17.984722+00:00
-- url     : https://prove2.me/theorems/65ac7ca9-bcf9-4314-b555-bc6c0b0ba76e
-- title:
--   Constraints: upper At iff run
-- statement:
--   Upper path judgments are membership in the upper run.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L405-L422
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L405-L422

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Constraints.upperAt_iff_run (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    UpperAt Γ π x y ↔ y ∈ Automata.upperRun Γ x π := by sorry
