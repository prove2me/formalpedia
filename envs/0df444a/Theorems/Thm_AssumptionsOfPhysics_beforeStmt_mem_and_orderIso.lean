-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_beforeStmt_mem_and_orderIso
-- name    : AssumptionsOfPhysics.beforeStmt_mem_and_orderIso
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T10:06:05.994419+00:00
-- url     : https://prove2.me/theorems/aa0dcf2b-561d-478c-a04c-14ad7ae1835f
-- title:
--   Before-statements are verifiable and ordered like the possibilities
-- statement:
--   Let $\le$ be a natural order on the possibilities $X$ of an experimental domain $\mathcal D$. Then for every $x_1\in X$ the statement $\text{“}x<x_1\text{”}=\bigvee_{x<x_1}x$ is a verifiable statement of $\mathcal D$, and $x_1\le x_2$ if and only if $\text{“}x<x_1\text{”}\preccurlyeq\text{“}x<x_2\text{”}$. In particular $(B_b,\preccurlyeq)$ is linearly ordered and order isomorphic to $(X,\le)$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Proposition 3.14, p. 175; Definition 3.12, p. 175

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem beforeStmt_mem_and_orderIso {Ω : Type*} (D : ExperimentalDomain Ω)
    (r : LinearOrder D.Possibility) (hr : D.IsNaturalOrder r) :
    (∀ x₁ : D.Possibility, D.beforeStmt r x₁ ∈ D.stmts) ∧
      ∀ x₁ x₂ : D.Possibility, r.le x₁ x₂ ↔ D.beforeStmt r x₁ ⊆ D.beforeStmt r x₂ := by sorry
end AssumptionsOfPhysics
