-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_saddle_center_neighborhood_transverse_winding
-- name    : BirkhoffGlobalSection.saddle_center_neighborhood_transverse_winding
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T00:46:51.191985+00:00
-- url     : https://prove2.me/theorems/c443e2b0-6097-4100-8357-176c24429031
-- title:
--   High Conley–Zehnder index near the equal-mass saddle-centers
-- statement:
--   High Conley–Zehnder index near the equal-mass saddle-centers.
--
--   At $\mu=\tfrac12$ and critical energy $c=2$, the first Lagrange point $l_1=(0,0)$ lifts to the two saddle-center points
--
--   $$
--   S_\pm=(\pm\tfrac12,0,0,0)
--   $$
--
--   of the Levi-Civita Hamiltonian, in the coordinates $(z_1,z_2,w_1,w_2)$. There exist an open set $U\subset\mathbb{R}^4$ containing $S_+$ and $S_-$ and radii $\varepsilon,\eta>0$ such that, whenever
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu).
--   $$
--
--   every closed orbit of the Levi-Civita flow on the selected component $\Sigma_{\mu,c}$ that enters $U$ has transverse winding above one. Equivalently, its Conley–Zehnder index is at least $3$.
--
--   This is Theorem 1.8 of Liu–Salomão with $\mu_0=\tfrac12$ and $N=3$, in the form used in Section 10 for energies below the first Lagrange value. Below that value there is no Lyapunov orbit, so no orbit has to be excluded. Together with the estimate away from $S_\pm$, it gives dynamical convexity in the critical strip.
--
--   **Formalization Note** Closed orbits are `IsPeriodicHamiltonianSolutionIn`, and the conclusion is `HasTransverseWindingAboveOne`, both from `Def_BirkhoffGlobalSection_DynamicalConvexity`. The source's bound "index $>3$" is weakened to "index $\ge3$".
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2. Theorem 1.8 (proved in Section 7) with mu_0 = 1/2 and N = 3, as applied in Section 10, first paragraph, to energies E < L_1(mu) near (1/2, -2).

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- High index near the saddle-centers. The points `(±1/2, 0, 0, 0)` are the
Levi-Civita lifts of the first Lagrange point for `μ = 1/2` at the critical
energy `c = 2`. Some open neighborhood of both points has the following
property for all parameters in a one-sided subcritical strip around `(1/2, 2)`:
every closed orbit of the selected component that meets it has transverse
winding above one. This is Theorem 1.8 of Liu--Salomao with `μ₀ = 1/2` and
`N = 3`, in the form used in Section 10; below the first critical value there
is no Lyapunov orbit to exclude. -/
theorem saddle_center_neighborhood_transverse_winding :
    ∃ U : Set Phase, IsOpen U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ U ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ U ∧
      ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            (∃ t : ℝ, x t ∈ U) →
            HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by sorry

end BirkhoffGlobalSection
