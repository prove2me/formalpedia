-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_not_hasUnaryObstruction_iff
-- name    : DeciSigma1.Full.Reduction.not_hasUnaryObstruction_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:46.935172+00:00
-- url     : https://prove2.me/theorems/881ea892-95e8-4461-8b3f-9d7a34ff789d
-- title:
--   Reduction: not has Unary Obstruction iff
-- statement:
--   The Reduction construction uses the not has Unary Obstruction iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L194-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L194-L200

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

theorem DeciSigma1.Full.Reduction.not_hasUnaryObstruction_iff (a : Closure.Config n V) :
    ¬ HasUnaryObstruction c Γ (a.1, a.2.1) a.2.2 ↔
      Disjoint (Automata.upperRun (signed c Γ) (a.1, a.2.1) a.2.2)
          (forbiddenPredecessors c Γ) ∧
      flipC a ∉ Closure.leastClosure c Γ := by sorry
