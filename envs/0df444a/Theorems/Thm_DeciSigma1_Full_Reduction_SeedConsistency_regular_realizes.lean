-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_SeedConsistency_regular_realizes
-- name    : DeciSigma1.Full.Reduction.SeedConsistency.regular_realizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:08:16.36478+00:00
-- url     : https://prove2.me/theorems/f0720aaf-d2a3-4740-82a2-ff4f2775992c
-- title:
--   Seed Consistency: regular realizes
-- statement:
--   For a satisfiable constraint, seeds and exclusions that satisfy `SeedConsistency` are realized
--   by a solution whose values are regular trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L397-L419
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L397-L419

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

theorem DeciSigma1.Full.Reduction.SeedConsistency.regular_realizes (hs : ∃ ρ, SatT c ρ Γ)
    {A B : Fin k → Closure.Config n V} (h : SeedConsistency c Γ A B) :
    ∃ ρ, (∀ v, Models.RegularTop (ρ v)) ∧ SatT c ρ Γ ∧ ∀ i,
      A i ∈ configSet c ρ ∧ B i ∉ configSet c ρ := by sorry
