-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_self_iff_event
-- name    : DeciSigma1.Full.Reduction.self_iff_event
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:52.095654+00:00
-- url     : https://prove2.me/theorems/6bc297af-f760-4b2b-b56d-7329f81dd520
-- title:
--   Reduction: self iff event
-- statement:
--   `Event c Γ a (flipC a)` holds exactly when `a` has a self-collision event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L203-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L203-L218

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
open DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}

theorem DeciSigma1.Full.Reduction.self_iff_event (a : Closure.Config n V) :
    Event c Γ a (flipC a) ↔
      ∃ i j, SelfCollisionEvent c Γ (a.1, a.2.1) a.2.2 i j := by sorry
