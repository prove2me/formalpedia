-- Prove2me | Theorems.Thm_DeciSigma1_Entailment_disjEntailsIn_iff_guarded_of_classes
-- name    : DeciSigma1.Entailment.disjEntailsIn_iff_guarded_of_classes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:19:26.999385+00:00
-- url     : https://prove2.me/theorems/c3cd00e5-86c5-46ff-8eab-b08dba5c36cd
-- title:
--   Entailment: disj Entails In iff guarded of classes
-- statement:
--   Disjunctive entailment over `{⊥, f}` is the entailment of the guarded constraint over
--   `{⊥, f, ⊤}` with a covariant constructor, for corresponding classes of trees: a class `C` of
--   trees over `{⊥, f}` in which every assignment lies below a guard `g ≤ f(g, …, g)` of `C`, and a
--   class `D` whose trees without `⊤` are the embeddings of the trees in `C`. The list `vs`
--   contains every variable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L119-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Entailment/Guard.lean#L119-L148

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

theorem DeciSigma1.Entailment.disjEntailsIn_iff_guarded_of_classes {C : PrefixSet n → Prop}
    {D : Semantics.Tree n → Prop} (hD : ∀ P, D P.toTree ↔ C P)
    (hC : ∀ ρ : V → PrefixSet n, (∀ v, C (ρ v)) →
      ∃ g, C g ∧ g ≤ PrefixSet.node (fun _ => g) ∧ ∀ v, ρ v ≤ g)
    {vs : List V} (hvs : ∀ v, v ∈ vs) (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn C Γ q ↔
      Full.DisjEntailsIn D (fun _ => false) (guarded vs Γ) (guardedQueries q) := by sorry
