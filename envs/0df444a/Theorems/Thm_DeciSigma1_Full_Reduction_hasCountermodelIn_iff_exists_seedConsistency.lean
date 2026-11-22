-- Prove2me | Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_iff_exists_seedConsistency
-- name    : DeciSigma1.Full.Reduction.hasCountermodelIn_iff_exists_seedConsistency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:11:45.774932+00:00
-- url     : https://prove2.me/theorems/215b3a90-f1bc-4cb0-bef7-b56834bcae9e
-- title:
--   Reduction: has Countermodel In iff exists seed Consistency
-- statement:
--   A satisfiable constraint has a countermodel to all queries exactly when, for some modes and
--   paths, the seeds and exclusions of the failures satisfy `SeedConsistency`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L449-L460
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Realization.lean#L449-L460

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

theorem DeciSigma1.Full.Reduction.hasCountermodelIn_iff_exists_seedConsistency (hs : ∃ ρ, SatT c ρ Γ) (q : Fin k → V × V) :
    HasCountermodelIn (fun _ => True) c Γ q ↔
      ∃ (m : Fin k → Bool) (W : Fin k → List (Fin n)),
        SeedConsistency c Γ (fun i => seed (q i) (m i) (W i))
          (fun i => exclusion (q i) (m i) (W i)) := by sorry
