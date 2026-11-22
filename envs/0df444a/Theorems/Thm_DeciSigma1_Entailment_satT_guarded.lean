-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_satT_guarded
-- name    : DeciSigma1.Entailment.satT_guarded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:21:41.249093+00:00
-- url     : https://prove2.me/theorems/ec05a4a0-d63d-4006-9ee0-95efaaa621ef
-- title:
--   Entailment: sat T guarded
-- statement:
--   An assignment satisfies the guarded constraint exactly when the value of the fresh
--   variable `u` satisfies `u ≤ f(u, …, u)`, the values of the variables in `vs` are below it, and the
--   literals of `Γ` hold.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L94-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L94-L112

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

theorem DeciSigma1.Entailment.satT_guarded (vs : List V) (Γ : List (Lit n V)) (σ : Option V → Semantics.Tree n) :
    SatT (fun _ => false) σ (guarded vs Γ) ↔
      σ none ≤ Semantics.Tree.node (fun _ => σ none) ∧ (∀ v ∈ vs, σ (some v) ≤ σ none) ∧
        ∀ l ∈ Γ, HoldsT (fun _ => false) (σ ∘ some) l.toLitT := by sorry
