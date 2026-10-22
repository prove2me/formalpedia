-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_retrograde_orbit_exists
-- name    : BirkhoffGlobalSection.birkhoff_retrograde_orbit_exists
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:09:55.5147+00:00
-- url     : https://prove2.me/theorems/b8b81f41-beb2-44d6-94a0-9e5687b1ead9
-- title:
--   Birkhoff's symmetric retrograde orbit
-- statement:
--   Let $0<\mu<1$ and $-c<h_1(\mu)$, and let $\varphi$ be the complete Levi-Civita Hamiltonian flow on $\Sigma_{\mu,c}$. There are a point $x\in\Sigma_{\mu,c}$ and a period $P>0$ representing a prime noncontractible quotient trajectory: $\varphi_P(x)=-x$, and no $0<t<P$ reaches either $x$ or $-x$. Its Jacobi projection is $q_2$-symmetric and, during $P$, its position is a simple collision-free loop of winding $+1$ around the chosen primary.
--
--   Liu--Salomão Theorem 5.1, attributed there to Birkhoff, supplies a $q_2$-symmetric retrograde orbit on each bounded regularized component for every $0<\mu<1$ and every energy below $L_1(\mu)$. In their terminology, a retrograde orbit projects to a simple closed curve around the primary moving opposite to the rotating system. Joung--van Koert Proposition 2.4 supplies the antipodal Levi-Civita covering interpretation used in this row. The separate double-lift theorem records the passage from this quotient-period representation to a least-period closed orbit upstairs.
-- source:
--   Liu--Salomão, Theorem 5.1 and the 2-unknotted retrograde-orbit discussion in Section 1.3, https://arxiv.org/abs/2506.17867v2; Joung--van Koert, Proposition 2.4, https://arxiv.org/abs/2407.19159v3, for the Levi-Civita covering interpretation.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Liu--Salomão, Theorem 5.1 (attributed there to Birkhoff), together with
their 2-unknotted description and the Levi-Civita covering interpretation of
Joung--van Koert, Proposition 2.4. -/
theorem birkhoff_retrograde_orbit_exists (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ δ : AntipodalPeriodicTrajectory φ,
      IsGeometricBirkhoffRetrogradeTrajectory φ δ := by sorry

end BirkhoffGlobalSection
