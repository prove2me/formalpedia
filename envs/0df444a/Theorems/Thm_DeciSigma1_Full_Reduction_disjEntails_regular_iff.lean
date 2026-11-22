-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_disjEntails_regular_iff
-- name    : DeciSigma1.Full.Reduction.disjEntails_regular_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:18:53.448501+00:00
-- url     : https://prove2.me/theorems/1743f71f-14a8-4ddd-ad12-03c79fcaf79a
-- title:
--   Reduction: disj Entails regular iff
-- statement:
--   Disjunctive entailment over `{⊥, f, ⊤}` holds over regular trees exactly when it holds over
--   arbitrary trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L103-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean#L103-L109

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

theorem DeciSigma1.Full.Reduction.disjEntails_regular_iff [Finite V] :
    DisjEntailsIn RegularTop c Γ q ↔ DisjEntailsIn (fun _ => True) c Γ q := by sorry
