-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_moves_dual
-- name    : DeciSigma1.Full.Closure.moves_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:47.831051+00:00
-- url     : https://prove2.me/theorems/d91c0ebb-00e7-481e-a500-2a6a3fb46e70
-- title:
--   Closure: moves dual
-- statement:
--   Exchanging the signs reverses a move derivation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L396-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L396-L400

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.moves_dual {p q : Config n V} (h : Moves c Γ p q) :
    Moves c Γ (flipC q) (flipC p) := by sorry
