-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_seedConsistency_hull_isSolution
-- name    : DeciSigma1.Full.Reduction.seedConsistency_hull_isSolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:11:32.89146+00:00
-- url     : https://prove2.me/theorems/83b9bc93-4272-4373-b256-4ecef5ed8662
-- title:
--   Reduction: seed Consistency hull is Solution
-- statement:
--   For a satisfiable constraint, under `SeedConsistency` the configurations derivable from the
--   facts and the seeds form a solution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L368-L393
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L368-L393

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

theorem DeciSigma1.Full.Reduction.seedConsistency_hull_isSolution (hs : ∃ ρ, SatT c ρ Γ) {A B : Fin k → Closure.Config n V}
    (h : SeedConsistency c Γ A B) : IsSolution c Γ (hull c Γ (Set.range A)) := by sorry
