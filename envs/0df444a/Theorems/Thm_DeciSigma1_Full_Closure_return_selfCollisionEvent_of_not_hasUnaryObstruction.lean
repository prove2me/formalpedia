-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_return_selfCollisionEvent_of_not_hasUnaryObstruction
-- name    : DeciSigma1.Full.Closure.return_selfCollisionEvent_of_not_hasUnaryObstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:04.162018+00:00
-- url     : https://prove2.me/theorems/2006ec8d-c7cd-47e6-85d9-6337795052ac
-- title:
--   Closure: return self Collision Event of not has Unary Obstruction
-- statement:
--   Without a unary obstruction, a derivation of the opposite sign at an extension of the path
--   gives a self-collision event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L492-L516
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L492-L516

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}
variable (c Γ)
variable {c Γ}

theorem DeciSigma1.Full.Closure.return_selfCollisionEvent_of_not_hasUnaryObstruction {p : V × Bool} {u δ : List (Fin n)}
    (hd : ¬ HasUnaryObstruction c Γ p u)
    (hr : Reach c Γ (p.1, p.2, u) (p.1, !p.2, u ++ δ)) :
    ∃ i j, SelfCollisionEvent c Γ p u i j := by sorry
