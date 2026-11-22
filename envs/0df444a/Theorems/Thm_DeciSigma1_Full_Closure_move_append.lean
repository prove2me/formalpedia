-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_move_append
-- name    : DeciSigma1.Full.Closure.move_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:53.019428+00:00
-- url     : https://prove2.me/theorems/dc9746a7-a0dc-4d9a-a2aa-9fdb935db88b
-- title:
--   Closure: move append
-- statement:
--   The Closure construction uses the move append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L402-L410
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L402-L410

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.move_append (σ : List (Fin n)) {p q : Config n V} (h : Move c Γ p q) :
    Move c Γ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by sorry
