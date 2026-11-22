-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_Reach_mem_of_closed
-- name    : DeciSigma1.Full.Closure.Reach.mem_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:38:45.620956+00:00
-- url     : https://prove2.me/theorems/27df4aeb-5f95-4ee9-b8a8-e8cec6369443
-- title:
--   Reach: mem of closed
-- statement:
--   The Reach construction uses the mem of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L348-L352
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L348-L352

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

theorem DeciSigma1.Full.Closure.Reach.mem_of_closed {a b : Config n V} {S : Set (Config n V)}
    (h : Reach c Γ a b) (hc : Closed c Γ S) (ha : a ∈ S) : b ∈ S := by sorry
