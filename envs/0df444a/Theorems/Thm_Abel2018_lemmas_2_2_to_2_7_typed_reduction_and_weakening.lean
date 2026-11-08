-- Prove2me | Theorems.Thm_Abel2018_lemmas_2_2_to_2_7_typed_reduction_and_weakening
-- name    : Abel2018.lemmas_2_2_to_2_7_typed_reduction_and_weakening
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:03.559774+00:00
-- url     : https://prove2.me/theorems/196a2584-3d6a-473f-8d60-dd95727d26f1
-- title:
--   Typed Weak-Head Reduction Properties, Typed Weakening, and Declarative EqRelSet Instance (Lemmas 2.2-2.7 & Section 3.1)
-- statement:
--   Section 2.2 (Lemmas 2.2-2.7) & Section 3.1 (`TermEq` instance of `EqRelSet`): Soundness of typed weak-head reduction (`Step` -> `TermEq`, `TypeStep` -> `TypeEq`), WHNF irreducibility, determinism of one-step weak-head reduction, typed weakening for all 4 declarative judgments (`TypeWf`, `HasType`, `TypeEq`, `TermEq`), and existence of the declarative judgmental equality `EqRelSet` instance (`synEqRel`, with `TypeEqRel = TypeEq`, `TermEqRel = TermEq`, and `NeEqRel = TermEq`).
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 2.2 (Lemmas 2.2-2.7) and Section 3.1 (`TermEq` instance of `EqRelSet`).

import Definitions.Def_Abel2018_Judgments

namespace Abel2018

theorem lemmas_2_2_to_2_7_typed_reduction_and_weakening :
    (∀ {Γ : Context} {t u A : Term}, Step Γ t u A → TermEq Γ t u A) ∧
    (∀ {Γ : Context} {A B : Term}, TypeStep Γ A B → TypeEq Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term}, Step Γ t u A → Whnf t → False) ∧
    (∀ {Γ : Context} {t u A u' A' : Term}, Step Γ t u A → Step Γ t u' A' → u = u') ∧
    (∀ {Γ Δ : Context} {A : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeWf Γ A → TypeWf Δ (wk ρ A)) ∧
    (∀ {Γ Δ : Context} {t A : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → HasType Γ t A → HasType Δ (wk ρ t) (wk ρ A)) ∧
    (∀ {Γ Δ : Context} {A B : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeEq Γ A B → TypeEq Δ (wk ρ A) (wk ρ B)) ∧
    (∀ {Γ Δ : Context} {t u A : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TermEq Γ t u A → TermEq Δ (wk ρ t) (wk ρ u) (wk ρ A)) ∧
    (∃ eqrel : EqRelSet,
      eqrel.TypeEqRel = TypeEq ∧
      eqrel.TermEqRel = TermEq ∧
      eqrel.NeEqRel = TermEq) := by sorry

end Abel2018
