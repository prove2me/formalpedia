-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_reach_iff_moves
-- name    : DeciSigma1.Full.Closure.reach_iff_moves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:38:25.60628+00:00
-- url     : https://prove2.me/theorems/cf32154c-4bbb-44e2-b193-6d607b9034a9
-- title:
--   Closure: reach iff moves
-- statement:
--   A derivation is a move derivation from an extension of its start.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L432-L445
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L432-L445

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.reach_iff_moves {v : V} {s : Bool} {u : List (Fin n)} {b : Config n V} :
    Reach c Γ (v, s, u) b ↔ ∃ α, Moves c Γ (v, s, u ++ α) b := by sorry
