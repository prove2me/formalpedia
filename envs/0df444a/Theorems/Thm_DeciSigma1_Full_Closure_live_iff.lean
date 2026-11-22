-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_live_iff
-- name    : DeciSigma1.Full.Closure.live_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:55.725253+00:00
-- url     : https://prove2.me/theorems/341008fc-31f5-4803-be13-39a0f19cfe67
-- title:
--   Closure: live iff
-- statement:
--   A configuration is live exactly when the configurations derivable from the facts and it avoid
--   the negative facts and are consistent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L475-L484
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L475-L484

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.live_iff {a : Config n V} :
    Live c Γ a ↔ Avoids Γ (seedClosure c Γ a) ∧ Consistent (seedClosure c Γ a) := by sorry
