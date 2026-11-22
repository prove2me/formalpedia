-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_hull_least
-- name    : DeciSigma1.Full.Closure.hull_least
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:39:39.028541+00:00
-- url     : https://prove2.me/theorems/c3ed71bd-c5ad-41e0-986a-44bc3f5c2df9
-- title:
--   Closure: hull least
-- statement:
--   The Closure construction uses the hull least property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L364-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L364-L368

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

theorem DeciSigma1.Full.Closure.hull_least {A S : Set (Config n V)} (hc : Closed c Γ S)
    (hf : ∀ ⦃p⦄, Fact Γ p → p ∈ S) (ha : A ⊆ S) : hull c Γ A ⊆ S := by sorry
