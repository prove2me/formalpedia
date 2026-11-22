-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_moves_append
-- name    : DeciSigma1.Full.Closure.moves_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:40:55.628897+00:00
-- url     : https://prove2.me/theorems/817f209d-8e00-40c4-9a83-1701dafbecaf
-- title:
--   Closure: moves append
-- statement:
--   Move derivations act at the head of the path and are unaffected by a common suffix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L413-L417
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L413-L417

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.moves_append (σ : List (Fin n)) {p q : Config n V} (h : Moves c Γ p q) :
    Moves c Γ (p.1, p.2.1, p.2.2 ++ σ) (q.1, q.2.1, q.2.2 ++ σ) := by sorry
