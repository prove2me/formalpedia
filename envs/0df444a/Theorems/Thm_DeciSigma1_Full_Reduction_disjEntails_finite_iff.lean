-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_finite_iff
-- name    : DeciSigma1.Full.Reduction.disjEntails_finite_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:02.042538+00:00
-- url     : https://prove2.me/theorems/30ea088c-29a8-4e1d-b235-e3a86b91ddaf
-- title:
--   Reduction: disj Entails finite iff
-- statement:
--   Disjunctive entailment over `{⊥, f, ⊤}` holds over finite trees exactly when `Γ` has no finite
--   solution or the entailment holds over arbitrary trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L113-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L113-L118

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

theorem DeciSigma1.Full.Reduction.disjEntails_finite_iff :
    DisjEntailsIn FiniteTop c Γ q ↔
      ¬ Models.SatFin c Γ ∨ DisjEntailsIn (fun _ => True) c Γ q := by sorry
