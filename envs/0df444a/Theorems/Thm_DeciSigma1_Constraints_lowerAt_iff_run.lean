-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_lowerAt_iff_run
-- name    : DeciSigma1.Constraints.lowerAt_iff_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:24:02.28789+00:00
-- url     : https://prove2.me/theorems/bf24d432-dc6b-401e-8c1b-8c2d7d0e4907
-- title:
--   Constraints: lower At iff run
-- statement:
--   Lower path judgments are membership in the lower run.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L385-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Constraints.lean#L385-L402

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem DeciSigma1.Constraints.lowerAt_iff_run (Γ : List (LitT n V)) (π : List (Fin n)) (x y : V) :
    LowerAt Γ π x y ↔ x ∈ Automata.lowerRun Γ y π := by sorry
