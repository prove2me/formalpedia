-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_seedClosure_subset
-- name    : DeciSigma1.Full.Closure.seedClosure_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:41:15.663804+00:00
-- url     : https://prove2.me/theorems/b3a285dd-795d-4a62-a83d-a1ffa5e0c6d3
-- title:
--   Closure: seed Closure subset
-- statement:
--   The Closure construction uses the seed Closure subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L469-L471
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L469-L471

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.seedClosure_subset {S : Set (Config n V)} {a : Config n V}
    (hS : IsSolution c Γ S) (ha : a ∈ S) : seedClosure c Γ a ⊆ S := by sorry
