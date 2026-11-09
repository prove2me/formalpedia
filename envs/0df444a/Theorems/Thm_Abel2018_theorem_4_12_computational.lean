-- Prove2me | Theorems.Thm_Abel2018_theorem_4_12_computational
-- name    : Abel2018.theorem_4_12_computational
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:34:20.175756+00:00
-- url     : https://prove2.me/theorems/298b9507-be9c-44f2-a0c4-2ad426e16b96
-- title:
--   Computational Adequacy of the Fuel-Bounded Lean Conversion Checkers (Based on Theorem 4.12)
-- statement:
--   Main Goal — Computational adequacy of the fuel-bounded Lean conversion checkers `compareTypeUp` and `compareTermUp` (based on Theorem 4.12): for all well-formed types `TypeWf Γ A`, `TypeWf Γ B` and well-typed terms `HasType Γ t A`, `HasType Γ u A`, there exists a finite fuel budget at which `compareTypeUp` / `compareTermUp` terminates with `some b`, and for every fuel budget at which it returns `some b`, `b = true` holds if and only if declarative equality (`TypeEq Γ A B` / `TermEq Γ t u A`) holds.
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 4.3 (Theorem 4.12; computational adequacy of the fuel-bounded Lean conversion checker).

import Definitions.Def_Abel2018_LogicalRelation

namespace Abel2018

theorem theorem_4_12_computational :
    (∀ (Γ : Context) (A B : Term), TypeWf Γ A → TypeWf Γ B →
      (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
      (∀ fuel b, compareTypeUp fuel Γ A B = some b →
        (b = true ↔ TypeEq Γ A B))) ∧
    (∀ (Γ : Context) (t u A : Term), HasType Γ t A → HasType Γ u A →
      (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
      (∀ fuel b, compareTermUp fuel Γ t u A = some b →
        (b = true ↔ TermEq Γ t u A))) := by sorry

end Abel2018
