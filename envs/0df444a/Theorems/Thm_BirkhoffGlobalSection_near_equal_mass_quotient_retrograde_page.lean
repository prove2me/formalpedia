-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_near_equal_mass_quotient_retrograde_page
-- name    : BirkhoffGlobalSection.near_equal_mass_quotient_retrograde_page
-- status  : Open
-- author  : @caleb
-- created : 2026-09-26T20:42:07.101048+00:00
-- url     : https://prove2.me/theorems/923eec94-d34d-4156-b3dc-5e5584a457b3
-- title:
--   Near-equal-mass quotient retrograde page (source-model existence)
-- statement:
--   This is the quotient-level form of the single-page consequence of Liu--Salomao Theorem 1.16(ii).
--
--   Let $\Sigma_{\mu,c}$ denote the selected Levi-Civita component with Jacobi energy $-c$, and let $h_1(\mu)$ be the first critical value. There is a mass neighborhood, uniform over all subcritical energies, such that
--
--   $$
--   \exists\varepsilon_0>0\quad\forall\mu,c,\qquad
--   0<\mu<1,\quad |\mu-\tfrac12|<\varepsilon_0,\quad -c<h_1(\mu)
--   $$
--
--   implies the following: for every complete Levi-Civita Hamiltonian flow $\varphi$ with antipodal equivariance, and every geometric Birkhoff retrograde antipodal trajectory $\delta$ (collision-free simple projected loop of winding $+1$ with $q_2$-reflection symmetry), the closed double lift $\gamma_\delta$ bounds a rational disk-like global surface of section in the antipodal quotient. That is, there is a smooth embedded immersed disk whose quotient interior is embedded and disjoint from the binding, whose boundary maps two-to-one onto the prime quotient binding with exactly antipodal identifications, which is transverse to the descended flow, and which every nonbinding quotient trajectory meets at arbitrarily large positive and negative times.
--
--   This isolates the analytic core of the transport obligation: the elliptic--hyperbolic model of Section 9.2, the regularization identification, and the positive-time-change preservation of transversality and returns, all stated at the quotient level where Liu--Salomao's conclusion naturally lands.
--
--   **Formalization Note** Lean states the conclusion with the mission's `RationalDiskLikeGlobalSurfaceOfSection` predicate applied to `antipodalTrajectoryDoubleLift`.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Theorem 1.16(ii), Section 9.2 and Section 10.

import Definitions.Def_BirkhoffGlobalSection

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The universal single-page conclusion of Liu--Salomao, Theorem 1.16(ii),
at the level of the Moser-regularized antipodal quotient: a uniform mass
neighborhood over all subcritical energies in which every geometric Birkhoff
retrograde trajectory has a rational disk-like page on its closed double lift. -/
theorem near_equal_mass_quotient_retrograde_page :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε₀ → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry

end BirkhoffGlobalSection
