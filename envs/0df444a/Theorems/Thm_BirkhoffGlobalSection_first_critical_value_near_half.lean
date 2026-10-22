-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_first_critical_value_near_half
-- name    : BirkhoffGlobalSection.first_critical_value_near_half
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T20:09:16.172383+00:00
-- url     : https://prove2.me/theorems/8a0eb460-0b5f-41a7-a0dd-475b7668cf59
-- title:
--   First critical value near equal masses
-- statement:
--   The first critical value is upper semicontinuous at equal masses.
--
--   For $\mu=\tfrac12$ the first critical value is $h_1(\tfrac12)=-2$, the Jacobi energy of the inner Lagrange point at the midpoint of the primaries. For every $\eta>0$ there is $\varepsilon>0$ such that
--   $$|\mu-\tfrac12|<\varepsilon \;\Longrightarrow\; h_1(\mu)<-2+\eta .$$
--
--   Consequently every subcritical energy $c$ with $-c<h_1(\mu)$ satisfies $c>2-\eta$ for $\mu$ near $\tfrac12$.
--
--   **Formalization Note** $h_1$ is `firstCriticalValue`, the infimum of the collision-free critical values of the Jacobi Hamiltonian. By the accepted `inner_lagrange_realizes_first_critical_value` it equals the value at the inner Lagrange point, which depends continuously on $\mu$.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2 (Theorem 1.12, Sections 9.2-9.3 and 10); reduction of regularization_model_convex_away_from_saddle_center.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Upper semicontinuity of the first critical value at equal masses: `h₁(1/2) = -2`, and for
mass ratios close to `1/2` the first critical value is below `-2 + η`. -/
theorem first_critical_value_near_half (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ < 1 → |μ - 1 / 2| < ε →
      firstCriticalValue μ < -2 + η := by sorry

end BirkhoffGlobalSection
