-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_true_of_hasCountermodelIn
-- name    : DeciSigma1.Full.Reduction.hasCountermodelIn_true_of_hasCountermodelIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:18.261912+00:00
-- url     : https://prove2.me/theorems/b79bc030-e0ca-402e-8c54-d581ab499042
-- title:
--   Reduction: has Countermodel In true of has Countermodel In
-- statement:
--   The Reduction construction uses the has Countermodel In true of has Countermodel In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L73-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L73-L77

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

theorem DeciSigma1.Full.Reduction.hasCountermodelIn_true_of_hasCountermodelIn {C : Semantics.Tree n → Prop}
    (h : HasCountermodelIn C c Γ q) :
    HasCountermodelIn (fun _ => True) c Γ q := by sorry
