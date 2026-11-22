-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_hasUnaryObstruction_iff_endpoint_or_leastClosure
-- name    : DeciSigma1.Full.Reduction.hasUnaryObstruction_iff_endpoint_or_leastClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:39.225775+00:00
-- url     : https://prove2.me/theorems/ef21c27f-e150-4c03-9aa5-be692c3f3304
-- title:
--   Reduction: has Unary Obstruction iff endpoint or least Closure
-- statement:
--   The Reduction construction uses the has Unary Obstruction iff endpoint or least Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L165-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L165-L192

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

theorem DeciSigma1.Full.Reduction.hasUnaryObstruction_iff_endpoint_or_leastClosure (p : V × Bool) (w : List (Fin n)) :
    HasUnaryObstruction c Γ p w ↔
      (Automata.upperRun (signed c Γ) p w ∩ forbiddenPredecessors c Γ).Nonempty ∨
      (p.1, !p.2, w) ∈ Closure.leastClosure c Γ := by sorry
