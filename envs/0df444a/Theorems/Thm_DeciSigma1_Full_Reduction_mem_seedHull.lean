-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_mem_seedHull
-- name    : DeciSigma1.Full.Reduction.mem_seedHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:06:38.176528+00:00
-- url     : https://prove2.me/theorems/2e4708a9-0c4b-436b-8fa4-34eaeb0dbdea
-- title:
--   Reduction: mem seed Hull
-- statement:
--   A configuration is derivable from the facts and the seeds `A` exactly when it lies in the
--   least closure or is derivable from a single seed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L282-L291
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L282-L291

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
omit [Fintype V] [DecidableEq V]

theorem DeciSigma1.Full.Reduction.mem_seedHull (A : Fin k → Closure.Config n V) (z : Closure.Config n V) :
    z ∈ hull c Γ (Set.range A) ↔ z ∈ leastClosure c Γ ∨ ∃ i, Reach c Γ (A i) z := by sorry
