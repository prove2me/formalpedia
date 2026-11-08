-- Prove2me | Theorems.Thm_Abel2018_theorems_4_5_and_4_12_decidability
-- name    : Abel2018.theorems_4_5_and_4_12_decidability
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T13:34:06.564261+00:00
-- url     : https://prove2.me/theorems/3ba3e0f5-af7c-4e00-89f2-dc827c764517
-- title:
--   Decidability of Algorithmic and Declarative Conversion (Theorems 4.5 & 4.12)
-- statement:
--   Section 4.2 (Theorem 4.5) & Section 4.3 (Theorem 4.12): Fuel-bounded executable decidability of algorithmic conversion (`compareTypeUp`, `compareTermUp`) on algorithmically reflexive inputs (`ConvTypeUp Γ A A`, `ConvTermUp Γ t t A`) and decidability (`P ∨ ¬P`) of declarative type and term equality (`TypeEq`, `TermEq`, corresponding to `dec` and `decTerm` in `Decidability.agda`).
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 4.2 (Theorem 4.5) and Section 4.3 (Theorem 4.12; `Decidability.agda`, `dec` and `decTerm`).

import Definitions.Def_Abel2018_LogicalRelation

namespace Abel2018

theorem theorems_4_5_and_4_12_decidability :
    (∀ {Γ Δ : Context} {A B : Term},
      ConvTypeUp Γ A A → ConvTypeUp Δ B B → CtxEq Γ Δ →
      ∃ fuel b, compareTypeUp fuel Γ A B = some b ∧
        (b = true ↔ ConvTypeUp Γ A B)) ∧
    (∀ {Γ Δ : Context} {t u A B : Term},
      ConvTermUp Γ t t A → ConvTermUp Δ u u B → CtxEq Γ Δ → TypeEq Δ A B →
      ∃ fuel b, compareTermUp fuel Γ t u A = some b ∧
        (b = true ↔ ConvTermUp Γ t u A)) ∧
    (∀ {Γ : Context} {A B : Term},
      TypeWf Γ A → TypeWf Γ B →
      TypeEq Γ A B ∨ ¬ TypeEq Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term},
      HasType Γ t A → HasType Γ u A →
      TermEq Γ t u A ∨ ¬ TermEq Γ t u A) := by sorry

end Abel2018
