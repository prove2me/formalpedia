-- Prove2me | Theorems.Thm_DeciSigma1_Full_not_disjEntailsIn_iff
-- name    : DeciSigma1.Full.not_disjEntailsIn_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:18.761172+00:00
-- url     : https://prove2.me/theorems/6d50c527-f66f-431d-8419-740a0d80cf83
-- title:
--   Full: not disj Entails In iff
-- statement:
--   A disjunctive entailment fails exactly when it has a countermodel in the class.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Basic.lean#L66-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Basic.lean#L66-L70

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n k : Nat} {V : Type}

theorem DeciSigma1.Full.not_disjEntailsIn_iff (C : Semantics.Tree n → Prop) (c : Fin n → Bool)
    (Γ : List (LitT n V)) (q : Fin k → V × V) :
    ¬ DisjEntailsIn C c Γ q ↔ HasCountermodelIn C c Γ q := by sorry
