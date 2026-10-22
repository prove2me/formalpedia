-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_position_coordinates_bounded
-- name    : BirkhoffGlobalSection.left_component_position_coordinates_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:23:59.861704+00:00
-- url     : https://prove2.me/theorems/c8641902-4557-4e0d-9ee0-745a045941f7
-- title:
--   Uniform position-coordinate bounds on the subcritical component
-- statement:
--   Let $0<\mu<1$, let $-c$ lie strictly below the first critical value, and let $\Sigma_{\mu,c}$ be the selected Levi-Civita component over the left primary. A state has coordinates $s=(z_1,z_2,w_1,w_2)$. There is a finite parameter-dependent number $R_z$ such that
--
--   $$
--   \forall s\in\Sigma_{\mu,c},\qquad |z_1|\leq R_z,\quad |z_2|\leq R_z.
--   $$
--
--   The bounded Hill-region component below the first critical energy confines the physical position; the Levi-Civita squaring relation $q+\mu=2z^2$ yields the corresponding bound on the regularized position coordinates. This is the position half of boundedness of the full four-dimensional component.
-- source:
--   Joung--van Koert, Section 2.1, Equation (2.2), and Proposition 2.4, https://arxiv.org/abs/2407.19159v3, PDF pp. 5–7. These are coordinatewise boundedness consequences for the selected subcritical star-shaped component, stated separately for position and momentum.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- At subcritical energy, the regularized position coordinates of the
selected component admit a uniform bound depending on the parameters. -/
theorem left_component_position_coordinates_bounded (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ Rz : ℝ, ∀ s ∈ leftEnergyComponent μ c,
      |s 0| ≤ Rz ∧ |s 1| ≤ Rz := by sorry

end BirkhoffGlobalSection
