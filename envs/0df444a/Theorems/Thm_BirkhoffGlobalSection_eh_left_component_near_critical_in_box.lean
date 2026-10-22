-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_left_component_near_critical_in_box
-- name    : BirkhoffGlobalSection.eh_left_component_near_critical_in_box
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T20:09:19.403104+00:00
-- url     : https://prove2.me/theorems/f1fe8e05-8519-437f-9610-b60e61da9a24
-- title:
--   Near-critical EH component lies in the convexity box off the saddle-centers
-- statement:
--   Localization of the selected EH component near the equal-mass critical energy.
--
--   Let $W$ be any open set containing the EH saddle-centers $\sigma_\pm=(0,\pm\tfrac{\pi}{2},0,0)$. Then there are $\varepsilon,\eta>0$ with the following property. Whenever
--   $$0<\mu<1,\qquad |\mu-\tfrac12|<\varepsilon,\qquad c<2+\eta,\qquad -c<h_1(\mu),$$
--   every point of the selected EH component $\Sigma^{EH}_{\mu,c}$ outside $W$ lies in the compact box
--   $$\cosh^2x_1\le 4,\qquad |x_2|\le\tfrac{\pi}{2},\qquad |y_1|,|y_2|\le 12 .$$
--
--   Below the first critical value the left Hill region is separated from the right one. As $(\mu,c)\to(\tfrac12,2)$ the component converges to the left lobe of the critical surface, and it leaves the region $|x_2|\le\pi/2$ only through a small neck around $\sigma_\pm$. The box is the one on which the critical convexity estimate holds.
--
--   **Formalization Note** `ehLeftEnergyComponent` is the connected component of the EH zero set through the collision point; it is the image of the Levi-Civita component under the EH regularization (accepted `eh_left_regularization_subcritical`).
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2 (Theorem 1.12, Sections 9.2-9.3 and 10); reduction of regularization_model_convex_away_from_saddle_center.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Localization of the selected EH component near the equal-mass critical energy: given any
open set containing the two EH saddle-centers `(0, ±π/2, 0, 0)`, for subcritical parameters
in a small strip around `(1/2, 2)` every point of the selected EH component outside the set
lies in the compact box `cosh² x₁ ≤ 4`, `|x₂| ≤ π/2`, `|y₁|, |y₂| ≤ 12`. -/
theorem eh_left_component_near_critical_in_box (W : Set Phase) (hW : IsOpen W)
    (hplus : (![0, Real.pi / 2, 0, 0] : Phase) ∈ W)
    (hminus : (![0, -(Real.pi / 2), 0, 0] : Phase) ∈ W) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
        ∀ y ∈ ehLeftEnergyComponent μ c, y ∉ W →
          Real.cosh (y 0) ^ 2 ≤ 4 ∧ |y 1| ≤ Real.pi / 2 ∧ |y 2| ≤ 12 ∧ |y 3| ≤ 12 := by sorry

end BirkhoffGlobalSection
