-- Prove2me | Theorems.Thm_Abel2018_lemma_4_3_and_theorem_4_11_soundness_and_completeness
-- name    : Abel2018.lemma_4_3_and_theorem_4_11_soundness_and_completeness
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:52.26183+00:00
-- url     : https://prove2.me/theorems/15d07ddf-4ec0-472e-87dc-ac71626b5347
-- title:
--   Soundness, Symmetry, Transitivity, Algorithmic EqRelSet Instance, and Completeness of Algorithmic Conversion (Lemma 4.3 & Theorem 4.11)
-- statement:
--   Section 4.1 (Lemma 4.3) & Section 4.3 (Theorem 4.11 & `Conv` instance of `EqRelSet`): Soundness, symmetry, and transitivity of algorithmic conversion (`ConvTypeUp`, `ConvTermUp`), existence of the algorithmic conversion `EqRelSet` instance (`convEqRel`, with `TypeEqRel = ConvTypeUp`, `TermEqRel = ConvTermUp`, and `NeEqRel = ConvNeEq`), and completeness of algorithmic conversion (`TypeEq` -> `ConvTypeUp`, `TermEq` -> `ConvTermUp`).
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 4.1 (Lemma 4.3) and Section 4.3 (Theorem 4.11 and `Conv` instance of `EqRelSet`; `Soundness.agda`, `SymmTrans.agda`, `Completeness.agda`).

import Definitions.Def_Abel2018_LogicalRelation

namespace Abel2018

theorem lemma_4_3_and_theorem_4_11_soundness_and_completeness :
    (∀ {Γ : Context} {A B : Term}, ConvTypeUp Γ A B → TypeEq Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term}, ConvTermUp Γ t u A → TermEq Γ t u A) ∧
    (∀ {Γ : Context} {A B : Term}, ConvTypeUp Γ A B → ConvTypeUp Γ B A) ∧
    (∀ {Γ : Context} {t u A : Term}, ConvTermUp Γ t u A → ConvTermUp Γ u t A) ∧
    (∀ {Γ : Context} {A B C : Term}, ConvTypeUp Γ A B → ConvTypeUp Γ B C → ConvTypeUp Γ A C) ∧
    (∀ {Γ : Context} {t u v A : Term}, ConvTermUp Γ t u A → ConvTermUp Γ u v A → ConvTermUp Γ t v A) ∧
    (∃ eqrel : EqRelSet,
      eqrel.TypeEqRel = ConvTypeUp ∧
      eqrel.TermEqRel = ConvTermUp ∧
      eqrel.NeEqRel = ConvNeEq) ∧
    (∀ {Γ : Context} {A B : Term}, TypeEq Γ A B → ConvTypeUp Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term}, TermEq Γ t u A → ConvTermUp Γ t u A) := by sorry

end Abel2018
