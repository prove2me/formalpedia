-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quotient_retrograde_page_local_subcritical
-- name    : BirkhoffGlobalSection.quotient_retrograde_page_local_subcritical
-- status  : Open
-- author  : @caleb
-- created : 2026-09-26T21:06:53.305261+00:00
-- url     : https://prove2.me/theorems/01bbb13c-b45f-4a9e-ba86-b95380123726
-- title:
--   Rational retrograde pages near each fixed regular equal-mass energy
-- statement:
--   Let $\Sigma_{\mu,c}$ be the selected Levi-Civita component and let $h_1(\mu)$ be the first critical value, with physical energy $E=-c$. In the parameter range below, every complete Levi-Civita Hamiltonian flow on this component that commutes with the antipodal action, and every geometric Birkhoff retrograde trajectory of that flow, has a rational disk-like global surface of section on its closed double lift in the antipodal quotient.
--
--   Fix $c_0>2$. There exist $\varepsilon>0$ and $\eta>0$, possibly depending on $c_0$, such that the asserted conclusion holds whenever
--
--   $$
--   0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad |c-c_0|<\eta,\qquad -c<h_1(\mu).
--   $$
--
--   This provides a local statement at each regular equal-mass energy. It does not require the neighborhood sizes to be uniform as the energy varies.
--
--   **Formalization Note** This is a specialized quotient-page consequence of the cited source argument, including its transport to the mission model. The conclusion uses the existing rational-page predicate with all its geometry, transversality, and two-sided return clauses.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10, third paragraph (open parameter neighborhood of the regular subcritical equal-mass line), and final paragraph (rational global sections); Theorems 1.12 and 1.16(ii).

import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

set_option autoImplicit false

theorem BirkhoffGlobalSection.quotient_retrograde_page_local_subcritical
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by sorry
