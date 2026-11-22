-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_reach_iff_event
-- name    : DeciSigma1.Full.Reduction.reach_iff_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:21.307197+00:00
-- url     : https://prove2.me/theorems/ab1700ed-4ebc-45fe-9e1b-034111ea5987
-- title:
--   Reduction: reach iff event
-- statement:
--   Without a unary obstruction at `a`, the configuration `a` derives `b` exactly when there is an
--   event from `a` to `b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L98-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L98-L101

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

theorem DeciSigma1.Full.Reduction.reach_iff_event (a b : Closure.Config n V)
    (ha : ¬ HasUnaryObstruction c Γ (a.1, a.2.1) a.2.2) :
    Reach c Γ a b ↔ Event c Γ a b := by sorry
