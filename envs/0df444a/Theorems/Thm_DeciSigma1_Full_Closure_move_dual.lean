-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_move_dual
-- name    : DeciSigma1.Full.Closure.move_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:42.8042+00:00
-- url     : https://prove2.me/theorems/e2fea0ea-6403-4e4a-822f-5b7134fe3f27
-- title:
--   Closure: move dual
-- statement:
--   Moves come in pairs: exchanging the signs reverses a move.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L385-L393
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L385-L393

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.move_dual {p q : Config n V} (h : Move c Γ p q) :
    Move c Γ (flipC q) (flipC p) := by sorry
