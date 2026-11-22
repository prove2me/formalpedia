-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_seedHull_cone_regular
-- name    : DeciSigma1.Full.Reduction.seedHull_cone_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:11:16.150854+00:00
-- url     : https://prove2.me/theorems/9762fad7-e8bd-465b-ab43-6c0828d5d11d
-- title:
--   Reduction: seed Hull cone regular
-- statement:
--   Under `SeedConsistency`, for every signed variable the set of paths at which it lies in the
--   hull of the seeds is regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L345-L356
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L345-L356

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

theorem DeciSigma1.Full.Reduction.seedHull_cone_regular {A B : Fin k → Closure.Config n V} (h : SeedConsistency c Γ A B)
    (q : V × Bool) : IsRegular {t | (q.1, q.2, t) ∈ hull c Γ (Set.range A)} := by sorry
