-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_regular_iff
-- name    : DeciSigma1.Entailment.disjEntailsIn_regular_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:20:15.727747+00:00
-- url     : https://prove2.me/theorems/413adbc8-8f35-4def-8ed1-6fd0e7923fb1
-- title:
--   Entailment: disj Entails In regular iff
-- statement:
--   Disjunctive entailment over `{⊥, f}` holds over regular trees exactly when it holds over
--   arbitrary trees.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L192-L199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L192-L199

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

theorem DeciSigma1.Entailment.disjEntailsIn_regular_iff [Finite V] (Γ : List (Lit n V))
    (q : Fin k → V × V) :
    DisjEntailsIn IsRegularTree Γ q ↔ DisjEntailsIn (fun _ => True) Γ q := by sorry
