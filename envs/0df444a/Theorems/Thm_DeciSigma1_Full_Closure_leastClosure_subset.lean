-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_leastClosure_subset
-- name    : DeciSigma1.Full.Closure.leastClosure_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:38:50.377354+00:00
-- url     : https://prove2.me/theorems/8976528d-1968-4d90-a811-e177a1493628
-- title:
--   Closure: least Closure subset
-- statement:
--   The Closure construction uses the least Closure subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L466-L467
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L466-L467

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.leastClosure_subset {S : Set (Config n V)} (hS : IsSolution c Γ S) : leastClosure c Γ ⊆ S := by sorry
