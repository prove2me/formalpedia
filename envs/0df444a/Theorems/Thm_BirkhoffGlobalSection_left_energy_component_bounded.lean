-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_bounded
-- name    : BirkhoffGlobalSection.left_energy_component_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:05:37.091513+00:00
-- url     : https://prove2.me/theorems/bed02756-fd7c-4b08-acdc-dd2185ac755a
-- title:
--   Boundedness of the selected regularized energy component
-- statement:
--   Let $0<\mu<1$, let the energy $-c$ lie below the first critical value, and let $\Sigma_{\mu,c}$ be the selected connected component of the regular Levi-Civita energy level in the four-dimensional phase space. Its position and momentum coordinates obey some uniform bound, expressed by boundedness of the set:
--
--   $$
--   \exists R>0\;\forall s\in\Sigma_{\mu,c},\quad\|s\|\leq R.
--   $$
--
--   The bound may depend on $\mu$ and $c$. It supplies the boundedness half of the compactness argument. Proposition 2.4 obtains the component as a star-shaped three-sphere below the critical energy, which is necessarily bounded.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7. These are the closedness and boundedness obligations underlying compactness of the star-shaped Levi-Civita three-sphere component.

import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The selected subcritical component has uniformly bounded Levi-Civita
position and momentum coordinates. -/
theorem left_energy_component_bounded (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    Bornology.IsBounded (leftEnergyComponent μ c) := by sorry

end BirkhoffGlobalSection
