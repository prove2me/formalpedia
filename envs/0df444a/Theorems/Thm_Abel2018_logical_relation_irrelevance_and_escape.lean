-- Prove2me | Theorems.Thm_Abel2018_logical_relation_irrelevance_and_escape
-- name    : Abel2018.logical_relation_irrelevance_and_escape
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:15.407208+00:00
-- url     : https://prove2.me/theorems/6823e9ee-4bb8-4107-96ba-1644007ca2af
-- title:
--   Logical-Relation Bundle Coherence, Level Irrelevance, and Escape Lemmas (Section 3.2, Lemmas 3.6 & 3.9)
-- statement:
--   Section 3.2 (Lemmas 3.6 & 3.9): Relation-bundle coherence (`irrelLogRel`: any two admissible `RedRel` bundles `rel₁`, `rel₂` derived via `LogRelAt eqrel l₁ Γ A rel₁` and `LogRelAt eqrel l₂ Γ A rel₂` across arbitrary levels `l₁, l₂ : TypeLevel` satisfy `RedRelEquiv rel₁ rel₂`), proof and level irrelevance of the decoded predicates (`irrelevanceEq`, `irrelevanceTerm`, `irrelevanceEqTerm`), and the four escape lemmas (`escape`, `escapeEq`, `escapeTerm`, `escapeTermEq`) connecting reducibility back to syntactic formation/typing and `eqrel` equality.
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 3.2 (Lemmas 3.6 and 3.9; `Irrelevance.agda` and `Escape.agda`).

import Definitions.Def_Abel2018_LogicalRelation

namespace Abel2018

theorem logical_relation_irrelevance_and_escape (eqrel : EqRelSet) :
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A : Term} {rel₁ rel₂ : RedRel},
      LogRelAt eqrel l₁ Γ A rel₁ →
      LogRelAt eqrel l₂ Γ A rel₂ →
      RedRelEquiv rel₁ rel₂) ∧
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A B : Term}
      (p : RedType eqrel l₁ Γ A) (q : RedType eqrel l₂ Γ A),
      RedEq p B → RedEq q B) ∧
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A t : Term}
      (p : RedType eqrel l₁ Γ A) (q : RedType eqrel l₂ Γ A),
      RedTerm p t → RedTerm q t) ∧
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A t u : Term}
      (p : RedType eqrel l₁ Γ A) (q : RedType eqrel l₂ Γ A),
      RedTermEq p t u → RedTermEq q t u) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A : Term},
      RedType eqrel l Γ A → TypeWf Γ A) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A B : Term} (p : RedType eqrel l Γ A),
      RedEq p B → eqrel.TypeEqRel Γ A B) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A t : Term} (p : RedType eqrel l Γ A),
      RedTerm p t → HasType Γ t A) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A t u : Term} (p : RedType eqrel l Γ A),
      RedTermEq p t u → eqrel.TermEqRel Γ t u A) := by sorry

end Abel2018
