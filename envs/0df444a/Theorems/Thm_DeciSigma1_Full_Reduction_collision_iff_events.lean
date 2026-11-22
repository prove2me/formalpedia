-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_collision_iff_events
-- name    : DeciSigma1.Full.Reduction.collision_iff_events
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:07:53.358265+00:00
-- url     : https://prove2.me/theorems/62c8e4e2-3509-4064-80c4-ab4ef0fc3f5d
-- title:
--   Reduction: collision iff events
-- statement:
--   The Reduction construction uses the collision iff events property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L76-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L76-L90

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

theorem DeciSigma1.Full.Reduction.collision_iff_events (a b : Closure.Config n V) :
    Collision c Γ a b ↔ Event c Γ a (flipC b) ∨ Event c Γ b (flipC a) := by sorry
