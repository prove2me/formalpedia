-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_upperStep_eq_empty_of_disjoint
-- name    : DeciSigma1.Full.Reduction.upperStep_eq_empty_of_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:22.218474+00:00
-- url     : https://prove2.me/theorems/21868e2f-a5c7-4d49-b435-c454c8130b10
-- title:
--   Reduction: upper Step eq empty of disjoint
-- statement:
--   The Reduction construction uses the upper Step eq empty of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L144-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L144-L152

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

theorem DeciSigma1.Full.Reduction.upperStep_eq_empty_of_disjoint (P : Finset (V × Bool)) (l : Fin n)
    (h : Disjoint P (forbiddenPredecessors c Γ)) :
    Automata.upperStep (signed c Γ) P l = ∅ := by sorry
