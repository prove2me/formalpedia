-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_near_equal_mass_lifted_retrograde_page
-- name    : BirkhoffGlobalSection.near_equal_mass_lifted_retrograde_page
-- status  : Open
-- author  : @caleb
-- created : 2026-09-26T18:20:25.504748+00:00
-- url     : https://prove2.me/theorems/a0cca2c4-0447-4cf8-989f-0b1fbda50fd6
-- title:
--   Near-equal-mass lifted retrograde page: source theorem and transport obligation
-- statement:
--   Let $\Sigma_{\mu,c}$ denote the selected Levi-Civita component, with Jacobi energy $-c$, and let $h_1(\mu)$ be the first critical value in the mission's definitions. There is a mass neighborhood, uniform over all subcritical energies, such that
--
--   $$
--   \exists\varepsilon_0>0\quad\forall\mu,c,\qquad
--   0<\mu<1,\quad |\mu-\tfrac12|<\varepsilon_0,\quad -c<h_1(\mu)
--   $$
--
--   implies the following: for every complete antipodally equivariant Levi-Civita Hamiltonian flow and every geometric Birkhoff retrograde antipodal trajectory $\delta$, the closed double lift $\gamma_\delta$ admits a lifted rational page:
--
--   $$
--   \operatorname{LiftedRationalPage}(\varphi,\gamma_\delta).
--   $$
--
--   The page is a smooth embedded immersed disk upstairs, with boundary $\gamma_\delta$, transverse interior, and exactly the opposite-boundary antipodal identifications. Every nonbinding trajectory meets either deck lift of its interior at arbitrarily large positive and negative times. The geometric retrograde hypothesis uses the mission's collision-free simple projected loop, positive winding, and reflection symmetry.
--
--   This is an **open transport obligation** for the single-page consequence of Liu–Salomão Theorem 1.16(ii), not a claim that their theorem is already formalized in Levi-Civita coordinates. It includes identification of the relevant energy component and critical-energy convention, identification of the retrograde binding, lifting through the antipodal cover, smooth boundary parametrization, and preservation of transversality and unbounded returns under the positive change of time. The elliptic–hyperbolic model is described in their Section 9.2; the Levi-Civita covering interpretation is Joung–van Koert Proposition 2.4.
--
--   The universal binding statement can be used with any geometric retrograde orbit, independently of the separate orbit-existence theorem.
-- source:
--   Liu?Salom?o, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Theorem 1.16(ii), Section 9.2 and Section 10; Joung?van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4. The cover-level definitions and descent formulation are formalization interfaces; the model and positive-time-change transport are explicit obligations, not conclusions quoted verbatim from the source.

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection

/-- The universal single-page conclusion of Liu--Salomão, Theorem 1.16(ii),
lifted and transported to the Levi-Civita cover. This open obligation includes
the regularization identification and preservation of two-sided unbounded
return times under the positive time change. -/
theorem near_equal_mass_lifted_retrograde_page :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε₀ → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            Nonempty (LiftedRationalPage φ
              (antipodalTrajectoryDoubleLift φ hanti δ)) := by sorry

end BirkhoffGlobalSection
