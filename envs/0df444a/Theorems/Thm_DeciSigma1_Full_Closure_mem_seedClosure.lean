-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_mem_seedClosure
-- name    : DeciSigma1.Full.Closure.mem_seedClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:51.802805+00:00
-- url     : https://prove2.me/theorems/7056c296-2ee1-434e-8398-d11bbb07cac6
-- title:
--   Closure: mem seed Closure
-- statement:
--   The Closure construction uses the mem seed Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L462-L464
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L462-L464

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.mem_seedClosure {a b : Config n V} :
    b ∈ seedClosure c Γ a ↔ b ∈ leastClosure c Γ ∨ Reach c Γ a b := by sorry
