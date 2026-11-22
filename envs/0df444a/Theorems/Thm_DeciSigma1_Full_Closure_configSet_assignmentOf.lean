-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_configSet_assignmentOf
-- name    : DeciSigma1.Full.Closure.configSet_assignmentOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:38:16.96333+00:00
-- url     : https://prove2.me/theorems/8a575a0d-53a7-4689-997a-bb16afebff8e
-- title:
--   Closure: config Set assignment Of
-- statement:
--   The Closure construction uses the config Set assignment Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L325-L329
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L325-L329

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

theorem DeciSigma1.Full.Closure.configSet_assignmentOf (S : Set (Config n V))
    (hc : Closed c Γ S) (hd : Consistent S) :
    configSet c (assignmentOf S hc hd) = S := by sorry
