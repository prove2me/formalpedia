-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_finite_iff_guarded
-- name    : DeciSigma1.Entailment.disjEntailsIn_finite_iff_guarded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:41.568945+00:00
-- url     : https://prove2.me/theorems/182e34c0-4d5c-40c2-8dba-bc81de372e21
-- title:
--   Entailment: disj Entails In finite iff guarded
-- statement:
--   Disjunctive entailment over finite trees over `{⊥, f}` is the entailment of the guarded
--   constraint over finite trees over `{⊥, f, ⊤}`. The guard of finitely many finite trees is a
--   complete tree whose depth exceeds the length of all their constructor positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L178-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L178-L188

module
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Embedding
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Entailment_Guard
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Entailment
open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics
variable {n k : ℕ} {V : Type}

theorem DeciSigma1.Entailment.disjEntailsIn_finite_iff_guarded {vs : List V} (hvs : ∀ v, v ∈ vs)
    (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn IsFiniteTree Γ q ↔
      Full.DisjEntailsIn Full.Models.FiniteTop (fun _ => false) (guarded vs Γ)
        (guardedQueries q) := by sorry
