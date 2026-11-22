-- Prove2me | Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_pin_signDual_iff
-- name    : DeciSigma1.Full.Models.Signed.FinitePinning.pin_signDual_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:31.649846+00:00
-- url     : https://prove2.me/theorems/c307b2d6-62b8-4e01-b104-8c8c34199fd8
-- title:
--   Finite Pinning: pin sign Dual iff
-- statement:
--   The sign dual of `A` satisfies the bound on the copy of sign `s` exactly when `A` satisfies the
--   bound on the copy of sign `!s`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L184-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Signed/Transfer.lean#L184-L192

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
open DeciSigma1.Full.Models.Signed.FinitePinning
variable {V : Type*}

theorem DeciSigma1.Full.Models.Signed.FinitePinning.pin_signDual_iff (c : Fin n → Bool) (b : GroundBound n V) (s : Bool)
    (A : V × Bool → Semantics.Tree n) :
    (pin c b s).Holds (Constraints.Signed.dual A) ↔ (pin c b (!s)).Holds A := by sorry
