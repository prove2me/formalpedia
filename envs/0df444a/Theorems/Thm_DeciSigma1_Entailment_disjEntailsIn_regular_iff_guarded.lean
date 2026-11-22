-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_regular_iff_guarded
-- name    : DeciSigma1.Entailment.disjEntailsIn_regular_iff_guarded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:22:09.50943+00:00
-- url     : https://prove2.me/theorems/1929574e-4e45-4844-b1f4-d38597a02a5c
-- title:
--   Entailment: disj Entails In regular iff guarded
-- statement:
--   Disjunctive entailment over regular trees over `{⊥, f}` is the entailment of the guarded
--   constraint over regular trees over `{⊥, f, ⊤}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L167-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L167-L173

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

theorem DeciSigma1.Entailment.disjEntailsIn_regular_iff_guarded {vs : List V} (hvs : ∀ v, v ∈ vs)
    (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn IsRegularTree Γ q ↔
      Full.DisjEntailsIn Full.Models.RegularTop (fun _ => false) (guarded vs Γ)
        (guardedQueries q) := by sorry
