-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_TopFree_holdsT_toLitT
-- name    : DeciSigma1.Constraints.TopFree.holdsT_toLitT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:34.433032+00:00
-- url     : https://prove2.me/theorems/21ea1f75-96b7-4a60-b2e3-67f19b016e0b
-- title:
--   Top Free: holds T to Lit T
-- statement:
--   An assignment of trees over `{⊥, f}` satisfies a literal exactly when the embedded
--   assignment satisfies it over `{⊥, f, ⊤}` with a covariant constructor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L60-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L60-L71

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
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.TopFree
open DeciSigma1.Semantics
variable {n : ℕ} {V : Type}

theorem DeciSigma1.Constraints.TopFree.holdsT_toLitT (ρ : V → PrefixSet n) (l : Lit n V) :
    HoldsT (fun _ => false) (fun v => (ρ v).toTree) l.toLitT ↔ l.Holds ρ := by sorry
