-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_Consistent_not_flip
-- name    : DeciSigma1.Full.Closure.Consistent.not_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:18.517586+00:00
-- url     : https://prove2.me/theorems/21c8a69b-dac8-497d-b176-bf8f630a9215
-- title:
--   Consistent: not flip
-- statement:
--   A consistent set does not contain a configuration together with its opposite sign.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L512-L517
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L512-L517

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.Consistent.not_flip {S : Set (Config n V)} (hc : Consistent S)
    {v : V} {s : Bool} {w : List (Fin n)} (hp : (v, s, w) ∈ S) : (v, !s, w) ∉ S := by sorry
