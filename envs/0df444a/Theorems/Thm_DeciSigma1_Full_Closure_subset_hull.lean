-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_subset_hull
-- name    : DeciSigma1.Full.Closure.subset_hull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:25.89717+00:00
-- url     : https://prove2.me/theorems/8ef38c40-3538-4a27-abf4-111cd50f4904
-- title:
--   Closure: subset hull
-- statement:
--   The Closure construction uses the subset hull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L361-L362
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L361-L362

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

theorem DeciSigma1.Full.Closure.subset_hull (A : Set (Config n V)) : A ⊆ hull c Γ A := by sorry
