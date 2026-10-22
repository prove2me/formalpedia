-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_closed
-- name    : BirkhoffGlobalSection.left_energy_component_closed
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:05:40.586251+00:00
-- url     : https://prove2.me/theorems/62a69c93-0c29-475c-baf2-76c1aa84dbd4
-- title:
--   Closedness of the selected regularized energy component
-- statement:
--   Let $0<\mu<1$, let the energy $-c$ lie below the first critical value, and let $\Sigma_{\mu,c}$ be the selected connected component of the regular Levi-Civita energy level in the four-dimensional phase space. The component is closed as a subset of the *whole* Levi-Civita phase space:
--
--   $$
--   \Sigma_{\mu,c}\subset\mathbb R^4\quad\text{is closed}.
--   $$
--
--   This includes the nontrivial requirement that a sequence in the selected component cannot converge to the second-collision locus, which is excluded from the regular energy locus. It supplies the closedness half of the compactness argument; the source's star-shaped three-sphere description entails this property.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7. These are the closedness and boundedness obligations underlying compactness of the star-shaped Levi-Civita three-sphere component.

import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The selected subcritical component is closed in the full Levi-Civita
phase space, including across the excluded second-collision locus. -/
theorem left_energy_component_closed (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsClosed (leftEnergyComponent μ c) := by sorry

end BirkhoffGlobalSection
