-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_collision_return
-- name    : DeciSigma1.Full.Closure.collision_return
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:06.394144+00:00
-- url     : https://prove2.me/theorems/2d014cc6-cb08-4584-8fb4-1274f07f3ef4
-- title:
--   Closure: collision return
-- statement:
--   If `a` and a seed derive the two signs of one configuration, then `a` derives the opposite sign
--   of an extension of the seed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L504-L509
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L504-L509

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.collision_return {a : Config n V} {h q : V} {s s' : Bool} {w v : List (Fin n)}
    (h₁ : Reach c Γ a (h, s, w)) (h₂ : Reach c Γ (q, s', v) (h, !s, w)) :
    ∃ δ, Reach c Γ a (q, !s', v ++ δ) := by sorry
