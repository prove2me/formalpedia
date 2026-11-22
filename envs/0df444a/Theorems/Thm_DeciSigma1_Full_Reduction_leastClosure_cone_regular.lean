-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_leastClosure_cone_regular
-- name    : DeciSigma1.Full.Reduction.leastClosure_cone_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:10:59.94873+00:00
-- url     : https://prove2.me/theorems/c2741946-e962-41be-bf96-72b0ec2426ba
-- title:
--   Reduction: least Closure cone regular
-- statement:
--   For every signed variable, the set of paths at which it lies in the least closure is
--   regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L297-L315
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L297-L315

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
variable {n k : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
omit [DecidableEq V]
omit [Fintype V]

theorem DeciSigma1.Full.Reduction.leastClosure_cone_regular [Finite V] (q : V × Bool) :
    IsRegular {t | (q.1, q.2, t) ∈ leastClosure c Γ} := by sorry
