-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_theoretical_eq_generated_basis
-- name    : AssumptionsOfPhysics.theoretical_eq_generated_basis
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T11:15:21.007008+00:00
-- url     : https://prove2.me/theorems/74611c7f-dcfb-445c-b5cd-329ff424054e
-- title:
--   A basis of the domain generates the theoretical domain
-- statement:
--   Let $B$ be any basis of the experimental domain $\mathcal D$. Then the theoretical domain $\bar{\mathcal D}$ coincides with the family of statements generated from $B$ by negation, finite conjunction and countable disjunction (equivalently, by De Morgan, negation, countable conjunction and countable disjunction). In particular the truth values of $B$ determine those of every theoretical statement.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.46, pp. 129–130

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem theoretical_eq_generated_basis {Ω : Type*} (D : ExperimentalDomain Ω)
    (B : Set (Set Ω)) (hB : IsBasis D.stmts B) :
    D.theoretical = {s | NegFinConjCountDisj B s} := by sorry
end AssumptionsOfPhysics
