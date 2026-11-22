-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_mem_leastClosure
-- name    : DeciSigma1.Full.Closure.mem_leastClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:38:53.701204+00:00
-- url     : https://prove2.me/theorems/78ce2313-94e7-46fb-94fe-f2ddf3aa8e12
-- title:
--   Closure: mem least Closure
-- statement:
--   The Closure construction uses the mem least Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L458-L460
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L458-L460

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.mem_leastClosure {b : Config n V} :
    b ∈ leastClosure c Γ ↔ ∃ a, Fact Γ a ∧ Reach c Γ a b := by sorry
