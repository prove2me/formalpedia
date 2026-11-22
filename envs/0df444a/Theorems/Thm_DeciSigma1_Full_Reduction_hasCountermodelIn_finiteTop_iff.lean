-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_finiteTop_iff
-- name    : DeciSigma1.Full.Reduction.hasCountermodelIn_finiteTop_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:17.335787+00:00
-- url     : https://prove2.me/theorems/73575d99-7112-4252-93c3-d7e8b72c2db4
-- title:
--   Reduction: has Countermodel In finite Top iff
-- statement:
--   The Reduction construction uses the has Countermodel In finite Top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L91-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L91-L99

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

theorem DeciSigma1.Full.Reduction.hasCountermodelIn_finiteTop_iff :
    HasCountermodelIn FiniteTop c Γ q ↔
      Models.SatFin c Γ ∧ HasCountermodelIn (fun _ => True) c Γ q := by sorry
