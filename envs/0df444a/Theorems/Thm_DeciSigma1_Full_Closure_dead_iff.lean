-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_dead_iff
-- name    : DeciSigma1.Full.Closure.dead_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:41:11.595783+00:00
-- url     : https://prove2.me/theorems/ad042253-8012-4662-86cd-d873404fa5c8
-- title:
--   Closure: dead iff
-- statement:
--   For a satisfiable constraint, a configuration is not live exactly when it derives a negative
--   fact, its opposite sign at an extension lies in the least closure, or it derives its own opposite
--   sign at an extension.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L522-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L522-L560

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*} {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Closure.dead_iff (hsat : Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ))
    {p : V} {s : Bool} {u : List (Fin n)} :
    ¬ Live c Γ (p, s, u) ↔
      (∃ n, Neg Γ n ∧ Reach c Γ (p, s, u) n) ∨
      (∃ δ, (p, !s, u ++ δ) ∈ leastClosure c Γ) ∨
      (∃ δ, Reach c Γ (p, s, u) (p, !s, u ++ δ)) := by sorry
