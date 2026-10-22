-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_geometric_retrograde_page_of_dynamical_convexity
-- name    : BirkhoffGlobalSection.geometric_retrograde_page_of_dynamical_convexity
-- status  : Open
-- author  : @caleb
-- created : 2026-09-28T00:46:40.897765+00:00
-- url     : https://prove2.me/theorems/f9b0ee2f-0152-4bc0-ad0d-d674411e3d61
-- title:
--   Retrograde rational pages from dynamical convexity
-- statement:
--   Retrograde rational pages from dynamical convexity.
--
--   Let $0<\mu<1$ and let $c$ be subcritical, $-c<h_1(\mu)$. Then the selected Levi-Civita component $\Sigma_{\mu,c}$ is a three-sphere that double covers the regularized component $\mathcal M_{\mu,c}\cong\mathbb{R}P^3$ under the antipodal map. Assume the Levi-Civita flow on $\Sigma_{\mu,c}$ is dynamically convex. Let $\varphi$ be a Levi-Civita Hamiltonian flow on $\Sigma_{\mu,c}$ that commutes with the antipodal map, let $\delta$ be a geometric Birkhoff retrograde trajectory, and let $\tilde\delta$ be its closed double lift. Then
--
--   $$
--   \Sigma_{\mu,c}\ \text{dynamically convex}\quad\Longrightarrow\quad \mathrm{LiftedRationalPage}(\varphi,\tilde\delta)\neq\varnothing .
--   $$
--
--   A lifted rational page has four properties.
--
--   1. It is a smooth immersed closed disk in $\Sigma_{\mu,c}$, injective on the closed disk, with boundary the orbit $\tilde\delta$.
--   2. Its interior is transverse to the flow.
--   3. It meets its antipodal image only at antipodal boundary points.
--   4. Every trajectory off $\tilde\delta$ hits the page or its antipodal image at arbitrarily large positive and negative times.
--
--   In the quotient it is a rational disk-like global surface of section bound by the retrograde orbit.
--
--   This is the binding step of Theorem 1.16(ii) of Liu–Salomão. It rests on the rational open book theorem for dynamically convex Reeb flows on $\mathbb{R}P^3$ (Hryniewicz–Salomão; Hryniewicz–Licata–Salomão) and on the fact that retrograde orbits are $2$-unknotted with self-linking number $-\tfrac12$. The statement holds at every subcritical parameter, so it combines with any dynamical convexity result.
--
--   **Formalization Note** Dynamical convexity is `IsDynamicallyConvexOn` from `Def_BirkhoffGlobalSection_DynamicalConvexity`, and the page is `LiftedRationalPage` on the Levi-Civita cover. The mass and energy hypotheses supply the regularity and the free antipodal symmetry of the component.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10, last paragraph (item (ii) of Theorem 1.16 from the cited rational open book results); Theorem 1.16(ii); Section 1.3, paragraph before Theorem 1.5 (retrograde orbits are 2-unknotted with self-linking number -1/2). Hryniewicz--Salomao, Elliptic bindings for dynamically convex Reeb flows on the real projective three-space, Calc. Var. PDE 55 (2016). Hryniewicz--Licata--Salomao, A dynamical characterization of universally tight lens spaces, Proc. London Math. Soc. 110 (2015).

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection

/-- The retrograde binding criterion under dynamical convexity. If the
Levi-Civita flow on the selected subcritical component is dynamically convex,
then the closed double lift of every geometric Birkhoff retrograde trajectory
bounds a lifted rational page. This combines the rational open book theorem for
dynamically convex Reeb flows on the real projective three-space with the fact
that the retrograde orbit is 2-unknotted with self-linking number `-1/2`, and
transports the resulting page to Levi-Civita coordinates. -/
theorem geometric_retrograde_page_of_dynamical_convexity
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (hdc : IsDynamicallyConvexOn (leviCivitaHamiltonian μ c)
      (leftEnergyComponent μ c))
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ)
    (δ : AntipodalPeriodicTrajectory φ)
    (hδ : IsGeometricBirkhoffRetrogradeTrajectory φ δ) :
    Nonempty (LiftedRationalPage φ
      (antipodalTrajectoryDoubleLift φ hanti δ)) := by sorry

end BirkhoffGlobalSection
