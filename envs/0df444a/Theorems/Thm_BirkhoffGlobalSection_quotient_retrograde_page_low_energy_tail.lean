-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quotient_retrograde_page_low_energy_tail
-- name    : BirkhoffGlobalSection.quotient_retrograde_page_low_energy_tail
-- status  : Open
-- author  : @caleb
-- created : 2026-09-26T21:06:52.223323+00:00
-- url     : https://prove2.me/theorems/c1a654bb-28ef-444e-8205-30a42725b099
-- title:
--   Rational retrograde pages on a uniform very-negative-energy tail
-- statement:
--   Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component and let $h_1(\mu)$ be the first critical value, with physical energy $E=-c$. In the parameter range below, every complete Levi-Civita Hamiltonian flow on this component that commutes with the antipodal action, and every geometric Birkhoff retrograde trajectory of that flow, has a rational disk-like global surface of section on its closed double lift in the antipodal quotient.
--
--   There exist $\varepsilon>0$ and a real cutoff $C$ such that the asserted conclusion holds whenever
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad C\le c,\qquad -c<h_1(\mu).
--   $$
--
--   This isolates uniformity at arbitrarily negative physical energy. The same mass radius applies throughout the tail; its cutoff is not prescribed.
--
--   **Formalization Note** This is a specialized quotient-page consequence of the cited source argument, including its transport to the mission model. The conclusion uses the existing rational-page predicate with all its geometry, transversality, and two-sided return clauses.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10, third paragraph, final sentence (uniform strict convexity for very negative energy), and final paragraph (rational global sections); Theorem 1.16(ii).

import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

set_option autoImplicit false

theorem BirkhoffGlobalSection.quotient_retrograde_page_low_energy_tail :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry
