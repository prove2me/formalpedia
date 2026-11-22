-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_crossClash_iff_collision
-- name    : DeciSigma1.Full.Reduction.crossClash_iff_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:55.505267+00:00
-- url     : https://prove2.me/theorems/d1fd0a80-0c65-4e67-8c8c-e9088abb4ad7
-- title:
--   Reduction: cross Clash iff collision
-- statement:
--   Without unary obstructions at `a` and `b`, the two configurations derive opposite signs of one
--   configuration exactly when they collide.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L105-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L105-L133

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Constraints DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Automata
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Reduction.crossClash_iff_collision (a b : Closure.Config n V)
    (ha : ¬ HasUnaryObstruction c Γ (a.1, a.2.1) a.2.2)
    (hb : ¬ HasUnaryObstruction c Γ (b.1, b.2.1) b.2.2) :
    CrossClash c Γ a b ↔ Collision c Γ a b := by sorry
