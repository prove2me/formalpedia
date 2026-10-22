-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_away_from_equal_mass_retrograde_global_section
-- name    : BirkhoffGlobalSection.away_from_equal_mass_retrograde_global_section
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-23T16:29:40.606304+00:00
-- url     : https://prove2.me/theorems/a09ca1d2-fa82-4632-9a45-8f36c94468a3
-- title:
--   Retrograde rational global sections away from equal masses
-- statement:
--   Let $0<\varepsilon\leq 1/2$ be any chosen radius around the equal-mass ratio. For every $0<\mu<1$ outside that interval, every subcritical energy, and every complete antipodally equivariant Levi-Civita Hamiltonian flow, there is a geometric retrograde orbit binding a rational global surface of section:
--
--   $$
--   |\mu-1/2|\geq\varepsilon \quad\Longrightarrow\quad
--   \exists\,\delta,\;\operatorname{GeometricRetrograde}(\delta)
--   \;\land\;\operatorname{RationalGSS}(\operatorname{DoubleLift}(\delta)).
--   $$
--
--   This is the complementary parameter subcase of Birkhoff's all-subcritical conjecture, after removing the near-equal-mass interval handled by Liu--Salomão Theorem 1.16(ii). It remains an open conjectural obligation for finite mass ratios; this statement does not assert that the complement has been proved.
--
--   **Formalization Note.** The quotient and page are the explicit cover-lift model of the mission's shared definitions; the flow and its equivariance are hypotheses.
-- source:
--   Birkhoff (1915), https://doi.org/10.1007/BF03015982; Liu--Salomão, Section 1.4 and Theorem 1.16(ii), https://arxiv.org/abs/2506.17867v2. This is the original open conjecture restricted to the complement of the known near-equal-mass interval.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The as-yet unresolved parameter region outside any chosen near-equal-mass
interval. This is the complementary subcase of the universal conjecture. -/
theorem away_from_equal_mass_retrograde_global_section
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (haway : ε ≤ |μ - 1 / 2|)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (hanti : IsAntipodallyEquivariantFlow μ c φ) :
    ∃ δ : AntipodalPeriodicTrajectory φ,
      IsGeometricBirkhoffRetrogradeTrajectory φ δ ∧
        RationalDiskLikeGlobalSurfaceOfSection φ hanti
          (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry

end BirkhoffGlobalSection
