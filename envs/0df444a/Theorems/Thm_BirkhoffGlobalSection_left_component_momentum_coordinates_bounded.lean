-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_momentum_coordinates_bounded
-- name    : BirkhoffGlobalSection.left_component_momentum_coordinates_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:24:06.679961+00:00
-- url     : https://prove2.me/theorems/6739053f-7c78-4d59-8515-f12c6cd75bac
-- title:
--   Uniform momentum-coordinate bounds on the subcritical component
-- statement:
--   Let $0<\mu<1$, let $-c$ lie strictly below the first critical value, and let $\Sigma_{\mu,c}$ be the selected Levi-Civita component over the left primary. A state has coordinates $s=(z_1,z_2,w_1,w_2)$. There is a finite parameter-dependent number $R_w$ such that
--
--   $$
--   \forall s\in\Sigma_{\mu,c},\qquad |w_1|\leq R_w,\quad |w_2|\leq R_w.
--   $$
--
--   This is the momentum half of boundedness of the full component. The zero-energy equation for the Levi-Civita Hamiltonian, combined with confinement to the selected subcritical region, provides the required uniform control. No particular numerical bound such as the separate narrow validated-parameter estimate is asserted.
-- source:
--   Joung--van Koert, Section 2.1, Equation (2.2), and Proposition 2.4, https://arxiv.org/abs/2407.19159v3, PDF pp. 5–7. These are coordinatewise boundedness consequences for the selected subcritical star-shaped component, stated separately for position and momentum.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- At subcritical energy, the regularized momentum coordinates of the
selected component admit a uniform bound depending on the parameters. -/
theorem left_component_momentum_coordinates_bounded (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ Rw : ℝ, ∀ s ∈ leftEnergyComponent μ c,
      |s 2| ≤ Rw ∧ |s 3| ≤ Rw := by sorry

end BirkhoffGlobalSection
