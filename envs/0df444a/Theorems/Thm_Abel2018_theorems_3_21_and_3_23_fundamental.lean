-- Prove2me | Theorems.Thm_Abel2018_theorems_3_21_and_3_23_fundamental
-- name    : Abel2018.theorems_3_21_and_3_23_fundamental
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:26.555206+00:00
-- url     : https://prove2.me/theorems/6954c33e-d347-45a2-9f26-c79deb466ddb
-- title:
--   Fundamental Theorem of the Logical Relation (Theorems 3.21 & 3.23)
-- statement:
--   Section 3.6 (Theorem 3.21 & Theorem 3.23): Fundamental theorem of the logical relation parameterized by `eqrel : EqRelSet` for all 5 declarative judgments (`FundCtxMotive`, `FundTypeMotive`, `FundTermMotive`, `FundTypeEqMotive`, `FundTermEqMotive`) and identity substitution validity, implying reducibility of well-formed types, well-typed terms, and judgmentally equal types and terms in any abstract equality system `eqrel`.
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 3.6 (Theorems 3.21 and 3.23; `Fundamental.agda`).

import Definitions.Def_Abel2018_LogicalRelation

namespace Abel2018

theorem theorems_3_21_and_3_23_fundamental (eqrel : EqRelSet) :
    (∀ {Γ : Context}, CtxWf Γ → FundCtxMotive eqrel Γ) ∧
    (∀ {Γ : Context} {A : Term}, TypeWf Γ A → FundTypeMotive eqrel Γ A) ∧
    (∀ {Γ : Context} {t A : Term}, HasType Γ t A → FundTermMotive eqrel Γ t A) ∧
    (∀ {Γ : Context} {A B : Term}, TypeEq Γ A B → FundTypeEqMotive eqrel Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term}, TermEq Γ t u A → FundTermEqMotive eqrel Γ t u A) ∧
    (∀ {Γ Δ : Context} {σ : Subst}, CtxWf Γ → CtxWf Δ → SubstWf Δ σ Γ →
      ValidCtx eqrel Γ ∧ ValidSubst eqrel Δ σ Γ) ∧
    (∀ {Γ Δ : Context} {σ σ' : Subst}, CtxWf Γ → CtxWf Δ → SubstEq Δ σ σ' Γ →
      ValidCtx eqrel Γ ∧ ValidSubst eqrel Δ σ Γ ∧ ValidSubst eqrel Δ σ' Γ ∧
      ValidSubstEq eqrel Δ σ σ' Γ) := by sorry

end Abel2018
