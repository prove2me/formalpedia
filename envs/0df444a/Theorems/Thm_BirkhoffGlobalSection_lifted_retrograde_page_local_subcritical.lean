-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lifted_retrograde_page_local_subcritical
-- name    : BirkhoffGlobalSection.lifted_retrograde_page_local_subcritical
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T01:17:32.676558+00:00
-- url     : https://prove2.me/theorems/0cdcc237-e188-453f-9c55-be6e651ae075
-- title:
--   Lifted retrograde pages near each fixed regular equal-mass energy
-- statement:
--   Fix $c_0 > 2$. There are $\varepsilon, \eta > 0$, possibly depending on $c_0$, such that whenever
--
--   $$
--   0 < \mu < 1, \qquad |\mu - \tfrac12| < \varepsilon, \qquad |c - c_0| < \eta, \qquad -c < h_1(\mu),
--   $$
--
--   every complete Levi-Civita Hamiltonian flow on the selected component that commutes with the antipodal action, and every geometric Birkhoff retrograde trajectory of that flow, admits a lifted rational two-disk page over its closed double lift, with all the geometry, transversality, and two-sided return clauses of the lifted-page predicate.
--
--   This is the cover-level local form of the universal lifted-page obligation, matching the quotient local statement above: via the proved descent theorem it implies the quotient local page. Like its siblings, it is a new conjecture formulated for this decomposition, motivated by the source argument including its transport to the mission model.
--
--   **Formalization Note** Uses the existing lifted-page predicate; existence is stated as `Nonempty` of the structure type.
-- source:
--   Local (per-energy) form of BirkhoffGlobalSection.near_equal_mass_lifted_retrograde_page, formulated for Prove2Me decomposition; motivated by Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10, Section 10 and Theorems 1.12, 1.16(ii). A new conjecture for the decomposition, not a claim made in that paper.

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection
theorem lifted_retrograde_page_local_subcritical
    (c₀ : ℝ) (hc₀ : 2 < c₀) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → |c - c₀| < η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            Nonempty (LiftedRationalPage φ
              (antipodalTrajectoryDoubleLift φ hanti δ)) := by sorry
end BirkhoffGlobalSection
