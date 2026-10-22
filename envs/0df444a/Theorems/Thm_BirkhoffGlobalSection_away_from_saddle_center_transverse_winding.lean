-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_away_from_saddle_center_transverse_winding
-- name    : BirkhoffGlobalSection.away_from_saddle_center_transverse_winding
-- status  : Open
-- author  : @caleb
-- created : 2026-09-28T00:47:02.999528+00:00
-- url     : https://prove2.me/theorems/cee3ae42-499c-4be3-96df-83544563bbdf
-- title:
--   Index bound away from the equal-mass saddle-centers
-- statement:
--   Index bound away from the equal-mass saddle-centers.
--
--   Let $U\subset\mathbb{R}^4$ be any open set containing the Levi-Civita saddle-center points $S_\pm=(\pm\tfrac12,0,0,0)$. These points lie over the first Lagrange point for $\mu=\tfrac12$ at the critical energy $c=2$. Then there exist $\varepsilon,\eta>0$ such that, whenever
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu).
--   $$
--
--   every closed orbit of the Levi-Civita flow on the selected component $\Sigma_{\mu,c}$ that stays outside $U$ has transverse winding above one. Equivalently, its Conley–Zehnder index is at least $3$.
--
--   This is the second half of the dynamical convexity argument near the critical energy in Liu–Salomão, Section 10. There it is derived from the strict convexity of the equal-mass critical surface away from $S_\pm$ (Theorem 1.12) and the index bound for strictly convex surfaces (Proposition 1.11). Together with the saddle-center estimate, it gives dynamical convexity in the critical strip.
--
--   **Formalization Note** The source states this for the neighborhood produced by Theorem 1.8. The argument applies to every open neighborhood of $S_\pm$, which is how it is stated here, and the radii depend on $U$. Closed orbits and the conclusion use `IsPeriodicHamiltonianSolutionIn` and `HasTransverseWindingAboveOne`.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10, first paragraph (orbits outside the neighborhood of the saddle-centers); Theorem 1.12 (strict convexity at mu = 1/2, E <= -2); Proposition 1.11 and Definition 1.10(ii).

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- Index bound away from the saddle-centers. Fix any open set containing the
Levi-Civita lifts `(±1/2, 0, 0, 0)` of the first Lagrange point for `μ = 1/2`.
For parameters in a small enough one-sided subcritical strip around `(1/2, 2)`,
every closed orbit of the selected component that avoids this set has
transverse winding above one. In Liu--Salomao, Section 10, this follows from
the strict convexity of the equal-mass critical surface (Theorem 1.12) through
the index argument of Proposition 1.11. -/
theorem away_from_saddle_center_transverse_winding
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ (x : ℝ → Phase) (T : ℝ),
          IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
            (leftEnergyComponent μ c) x T →
          (∀ t : ℝ, x t ∉ U) →
          HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by sorry

end BirkhoffGlobalSection
