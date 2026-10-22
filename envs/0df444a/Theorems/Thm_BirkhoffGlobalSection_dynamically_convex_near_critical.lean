-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_dynamically_convex_near_critical
-- name    : BirkhoffGlobalSection.dynamically_convex_near_critical
-- status  : Open
-- author  : @caleb
-- created : 2026-09-28T00:46:30.427706+00:00
-- url     : https://prove2.me/theorems/25833c39-d93e-4e28-a351-7a3022ecb651
-- title:
--   Dynamical convexity near the equal-mass critical energy
-- statement:
--   Dynamical convexity of the selected Levi-Civita component near the equal-mass critical energy.
--
--   Write $\Sigma_{\mu,c}$ for the selected Levi-Civita component: the regularized energy component over the primary at $q=(-\mu,0)$ at Jacobi energy $E=-c$. It carries the Levi-Civita Hamiltonian $K_{\mu,c}$. Let $h_1(\mu)$ be the first critical value. There exist $\varepsilon>0$ and $\eta>0$ such that the Hamiltonian flow of $K_{\mu,c}$ on $\Sigma_{\mu,c}$ is dynamically convex whenever
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu).
--   $$
--
--   Dynamical convexity means that every closed orbit on $\Sigma_{\mu,c}$, multiple covers included, has Conley–Zehnder index at least $3$ in the global quaternionic frame. This is the lifted form of dynamical convexity of the regularized $\mathbb{R}P^3$ component.
--
--   This is the first step of the proof of Theorem 1.16 in Liu–Salomão, and the part of Theorem 1.16(i) near the critical point $(\mu,E)=(\tfrac12,-2)$. It is the hypothesis under which retrograde orbits bind rational open books.
--
--   **Formalization Note** Dynamical convexity is `IsDynamicallyConvexOn` from `Def_BirkhoffGlobalSection_DynamicalConvexity`, applied to `leviCivitaHamiltonian μ c` on `leftEnergyComponent μ c`. The strip is one-sided in $c$ and is intersected with the subcritical region. Since $h_1(\mu)\to-2$ as $\mu\to\tfrac12$, it lies in a small neighborhood of $(\tfrac12,2)$ once $\varepsilon$ is small.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10 (proof of Theorem 1.16), first paragraph: dynamical convexity of the RP^3 components for (mu, E) close to (1/2, -2) with E < L_1(mu). Definition 1.10(i); Theorem 1.16(i).

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity

namespace BirkhoffGlobalSection

/-- Dynamical convexity near the equal-mass critical energy: in the one-sided
subcritical strip around `(μ, c) = (1/2, 2)`, every closed orbit of the
Levi-Civita flow on the selected component has transverse winding above one,
that is, Conley--Zehnder index at least `3`. This is the opening claim of the
proof of Theorem 1.16 in Liu--Salomao, Section 10, for the component around the
primary at `q = (-μ, 0)`. -/
theorem dynamically_convex_near_critical :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        IsDynamicallyConvexOn (leviCivitaHamiltonian μ c)
          (leftEnergyComponent μ c) := by sorry

end BirkhoffGlobalSection
