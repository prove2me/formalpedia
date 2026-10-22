-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_near_equal_mass_birkhoff_rational_global_section
-- name    : BirkhoffGlobalSection.near_equal_mass_birkhoff_rational_global_section
-- status  : Open
-- author  : @Yivy Yu
-- created : 2026-09-12T15:11:10.228161+00:00
-- url     : https://prove2.me/theorems/d5b5e464-9d3f-4ddb-85d3-a7f5947f1a36
-- title:
--   Theorem 1.16(ii) — near-equal-mass rational global sections
-- statement:
--   There exists $0<\varepsilon\leq1/2$ such that, whenever
--
--   $$
--   0<\mu<1,
--   \qquad
--   \left|\mu-\frac12\right|<\varepsilon,
--   \qquad
--   -c<h_1(\mu),
--   $$
--
--   the complete antipodally equivariant Levi-Civita Hamiltonian flow on $\Sigma_{\mu,c}$ has a geometric Birkhoff retrograde orbit whose prime image in the antipodal quotient binds a rational two-disk global surface of section.
--
--   This is an existential single-page consequence of Liu--Salomão Theorems 5.1 and 1.16(ii). Theorem 5.1 supplies a $q_2$-symmetric geometric retrograde orbit at every subcritical energy; Theorem 1.16(ii) proves, for mass ratios sufficiently close to $1/2$, that every retrograde orbit in either regularized component binds a rational open book whose pages are global surfaces of section. The paper works with elliptic--hyperbolic regularization and the associated Reeb flow. A proof of this Lean row must therefore also transport the result to the Levi-Civita antipodal quotient and verify preservation under the positive time change; that bridge is not silently treated as part of the cited theorem statement.
-- source:
--   Liu--Salomão, Theorems 5.1 and 1.16(ii), https://arxiv.org/abs/2506.17867v2. The Lean row also requires the model-transport and positive-time-change bridge from their elliptic--hyperbolic/Reeb formulation to the Levi-Civita antipodal quotient.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The existential single-page consequence of Liu--Salomão, Theorems 5.1 and
1.16(ii), transported to the Levi-Civita quotient model. A proof must include
the regularization and positive-time-change bridge between the two models. -/
theorem near_equal_mass_birkhoff_rational_global_section :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ hanti : IsAntipodallyEquivariantFlow μ c φ,
          ∃ δ : AntipodalPeriodicTrajectory φ,
            IsGeometricBirkhoffRetrogradeTrajectory φ δ ∧
              RationalDiskLikeGlobalSurfaceOfSection φ hanti
                (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry

end BirkhoffGlobalSection
