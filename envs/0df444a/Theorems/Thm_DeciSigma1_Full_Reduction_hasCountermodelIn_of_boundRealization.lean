-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_of_boundRealization
-- name    : DeciSigma1.Full.Reduction.hasCountermodelIn_of_boundRealization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:03.798795+00:00
-- url     : https://prove2.me/theorems/6b99adc6-69f9-44c4-987d-e56fab82fe2a
-- title:
--   Reduction: has Countermodel In of bound Realization
-- statement:
--   The Reduction construction uses the has Countermodel In of bound Realization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L63-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L63-L71

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n k : Nat} {V : Type}
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}

theorem DeciSigma1.Full.Reduction.hasCountermodelIn_of_boundRealization {C : Semantics.Tree n → Prop}
    (h : Signed.BoundRealization C c Γ) (hc : HasCountermodelIn (fun _ => True) c Γ q) :
    HasCountermodelIn C c Γ q := by sorry
