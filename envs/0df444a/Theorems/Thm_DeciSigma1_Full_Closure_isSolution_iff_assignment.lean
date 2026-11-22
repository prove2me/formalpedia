-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_isSolution_iff_assignment
-- name    : DeciSigma1.Full.Closure.isSolution_iff_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:30.106016+00:00
-- url     : https://prove2.me/theorems/3c95511a-a2d2-4d9a-b2c9-08055b1eb00c
-- title:
--   Closure: is Solution iff assignment
-- statement:
--   The Closure construction uses the is Solution iff assignment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L331-L338
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L331-L338

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ}
variable {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.isSolution_iff_assignment {S : Set (Config n V)} :
    IsSolution c Γ S ↔ ∃ ρ, SatT c ρ Γ ∧ configSet c ρ = S := by sorry
