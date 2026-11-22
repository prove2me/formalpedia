-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_reach_extend
-- name    : DeciSigma1.Full.Closure.reach_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:44.529144+00:00
-- url     : https://prove2.me/theorems/8bd20111-ac07-4a2b-a3c3-ea3c8f360d78
-- title:
--   Closure: reach extend
-- statement:
--   The Closure construction uses the reach extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L424-L429
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L424-L429

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.reach_extend (v : V) (s : Bool) (u α : List (Fin n)) :
    Reach c Γ (v, s, u) (v, s, u ++ α) := by sorry
