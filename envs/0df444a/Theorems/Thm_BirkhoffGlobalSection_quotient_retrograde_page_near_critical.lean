-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quotient_retrograde_page_near_critical
-- name    : BirkhoffGlobalSection.quotient_retrograde_page_near_critical
-- status  : Open
-- author  : @caleb
-- created : 2026-09-26T21:06:56.217984+00:00
-- url     : https://prove2.me/theorems/1dce2898-019e-4085-9d7f-6ad712d4e8a5
-- title:
--   Rational retrograde pages in a subcritical strip near the equal-mass critical energy
-- statement:
--   Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component and let $h_1(\mu)$ be the first critical value, with physical energy $E=-c$. In the parameter range below, every complete Levi-Civita Hamiltonian flow on this component that commutes with the antipodal action, and every geometric Birkhoff retrograde trajectory of that flow, has a rational disk-like global surface of section on its closed double lift in the antipodal quotient.
--
--   There exist $\varepsilon>0$ and $\eta>0$ such that the asserted conclusion holds whenever
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu).
--   $$
--
--   This isolates the critical-energy regime. The strip is one-sided and is always intersected with the subcritical region; it makes no assertion at or above the first critical energy.
--
--   **Formalization Note** This is a specialized quotient-page consequence of the cited source argument, including its transport to the mission model. The conclusion uses the existing rational-page predicate with all its geometry, transversality, and two-sided return clauses.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10, first two paragraphs (critical-energy index bounds), and final paragraph (rational global sections); Theorems 1.8, 1.12, and 1.16(ii). The one-sided subcritical strip also uses continuity of the first critical value at equal mass.

import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

set_option autoImplicit false

theorem BirkhoffGlobalSection.quotient_retrograde_page_near_critical :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry
