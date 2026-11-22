-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_not_live_iff_unaryObstruction_or_selfCollision
-- name    : DeciSigma1.Full.Closure.not_live_iff_unaryObstruction_or_selfCollision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:33.69394+00:00
-- url     : https://prove2.me/theorems/f4c73c5c-ce2a-4f8c-9b56-551efeab031c
-- title:
--   Closure: not live iff unary Obstruction or self Collision
-- statement:
--   For a satisfiable constraint, a configuration is not live exactly when it has a unary
--   obstruction or a self-collision event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L520-L537
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Automata.lean#L520-L537

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

theorem DeciSigma1.Full.Closure.not_live_iff_unaryObstruction_or_selfCollision
    (hsat : Avoids Γ (leastClosure c Γ) ∧ Consistent (leastClosure c Γ))
    {p : V × Bool} {u : List (Fin n)} :
    ¬ Live c Γ (p.1, p.2, u) ↔
      HasUnaryObstruction c Γ p u ∨ ∃ i j, SelfCollisionEvent c Γ p u i j := by sorry
