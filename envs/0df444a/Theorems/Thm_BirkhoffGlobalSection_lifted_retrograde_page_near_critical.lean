-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_lifted_retrograde_page_near_critical
-- name    : BirkhoffGlobalSection.lifted_retrograde_page_near_critical
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T14:27:01.020046+00:00
-- url     : https://prove2.me/theorems/2eb91cea-188b-4b47-9825-ac4b170ec1f5
-- title:
--   Rational retrograde pages on the cover near the critical energy
-- statement:
--   Cover-level rational retrograde pages in a subcritical strip near the equal-mass critical energy.
--
--   In the parameter range $0 < \mu < 1$ with $|\mu - \tfrac{1}{2}| < \varepsilon$, $c < 2 + \eta$, and $-c$ below the first critical value $h_1(\mu)$, every complete Levi-Civita Hamiltonian flow on the selected component that commutes with the antipodal action, and every geometric Birkhoff retrograde trajectory of that flow, has a rational page on its closed double lift in the cover:
--
--   $$
--   \exists \varepsilon > 0,\ \exists \eta > 0,\ \forall (\mu, c)\text{ in the strip},\ \forall \varphi, h_{anti}, \delta,\quad Nonempty~(LiftedRationalPage~\varphi~(doubleLift~\delta)).
--   $$
--
--   This is the cover-level core of the critical-energy argument of Section 10: the Conley--Zehnder index bounds at the critical energy produce the rational page upstairs, and the quotient statement follows by antipodal descent.
--
--   **Formalization Note** Lean states the one-sided strip with $c < 2 + \eta$ together with the subcritical hypothesis, concluding nonemptiness of the lifted rational page on the double lift.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10. Section 10, critical-energy index bounds; Theorems 1.8, 1.12, and 1.16(ii).

import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection

/-- The cover-level critical-energy page of Liu--Salomao, Section 10: in the
one-sided subcritical strip near the equal-mass critical energy, every
geometric Birkhoff retrograde trajectory has a rational page on its closed
double lift in the cover. Neither radius is asserted to be uniform beyond
the strip. -/
theorem lifted_retrograde_page_near_critical :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            Nonempty (LiftedRationalPage φ
              (antipodalTrajectoryDoubleLift φ hanti δ)) := by sorry
end BirkhoffGlobalSection
