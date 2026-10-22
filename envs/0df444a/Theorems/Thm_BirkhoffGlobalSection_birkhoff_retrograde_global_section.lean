-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_birkhoff_retrograde_global_section
-- name    : BirkhoffGlobalSection.birkhoff_retrograde_global_section
-- status  : Open
-- author  : @Yivy Yu
-- created : 2026-09-12T15:11:21.932959+00:00
-- url     : https://prove2.me/theorems/deae0f6b-c4a7-4155-9e1b-5271f7fc5f89
-- title:
--   Birkhoff's retrograde rational global-section conjecture
-- statement:
--   Let $0<\mu<1$ and let the Hamiltonian energy satisfy $-c<h_1(\mu)$. Let $\Sigma_{\mu,c}$ be the Levi-Civita component based at the collision over $q=(-\mu,0)$, and let $\varphi$ be its complete Hamiltonian flow, commuting with the antipodal deck map. Write
--
--   $$
--   Q_{\mu,c}=\Sigma_{\mu,c}/(s\sim -s).
--   $$
--
--   Joung--van Koert Proposition 2.4 identifies this antipodal quotient with the corresponding Moser-regularized $\mathbb{RP}^3$ component. Lean constructs the topological quotient itself; it does not install Moser coordinates or a smooth atlas on that quotient. Antipodal equivariance makes the descended time maps representative-independent, and their flow laws and joint continuity are part of the formal target. Smoothness and transversality are stated on the Levi-Civita lift.
--
--   There exists a prime noncontractible quotient trajectory, represented by a lift $x\in\Sigma_{\mu,c}$ and a period $P>0$, such that:
--
--   1. $\varphi_P(x)=-x$, while no $0<t<P$ reaches either $x$ or $-x$;
--   2. its Jacobi projection is $q_2$-symmetric, and during the period $P$ its position is a simple collision-free counterclockwise loop of winding $+1$ about the chosen primary; and
--   3. the quotient orbit binds a rational two-disk global surface of section.
--
--   Equivariance and freeness imply that traversing the trajectory twice gives a closed Levi-Civita orbit of least period $2P$. The third clause means that there is a map $f:D^2\to Q_{\mu,c}$ with a smooth immersive Levi-Civita lift $\widetilde f:D^2\to\Sigma_{\mu,c}$. The lifted disk is embedded, and its boundary is that full double-lifted orbit. The quotient interior is topologically embedded and disjoint from the binding. For closed-disk parameters $u,v$, the exact fibers are
--
--   $$
--   f(u)=f(v)
--   \iff
--   u=v\ \text{ or }\
--   u,v\in\partial D^2\ \text{ and }\ v=-u.
--   $$
--
--   Thus the boundary is exactly a two-fold cover of the prime quotient binding. The lifted page interior is transverse to the Hamiltonian vector field, and every quotient trajectory outside the binding meets the quotient interior at arbitrarily large positive and arbitrarily large negative times.
--
--   This is an existential, one-labeled-primary formulation of Birkhoff's retrograde global-section problem. It asks for one rational page, not an entire rational open-book fibration, and it uses Birkhoff's geometric shooting notion rather than the stronger all-time astronomical inequality of Joung--van Koert.
-- source:
--   Birkhoff, The restricted problem of three bodies (1915), https://doi.org/10.1007/BF03015982; Liu--Salomão, Section 1.4, https://arxiv.org/abs/2506.17867v2. This is the universal finite-mass, all-subcritical open target for one labeled primary.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- An existential, labeled-primary formulation of Birkhoff's retrograde-orbit
global-section problem. The rational page and all return conditions are stated
in the antipodal quotient, using a smooth Levi-Civita lift. -/
theorem birkhoff_retrograde_global_section (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ) :
    ∃ δ : AntipodalPeriodicTrajectory φ,
      IsGeometricBirkhoffRetrogradeTrajectory φ δ ∧
        RationalDiskLikeGlobalSurfaceOfSection φ hanti
          (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry

end BirkhoffGlobalSection
