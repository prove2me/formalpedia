-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_compact
-- name    : BirkhoffGlobalSection.left_energy_component_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T16:58:02.805508+00:00
-- url     : https://prove2.me/theorems/de41bf60-5b74-42d5-bb1a-ee00f18c2417
-- title:
--   Compactness of the subcritical Levi-Civita component
-- statement:
--   Let $0<\mu<1$ and let the Jacobi energy $-c$ lie strictly below the first critical value. Write $\Sigma_{\mu,c}$ for the connected component of the regular Levi-Civita energy level based at the regularized collision over the left primary. The selected component is compact:
--
--   $$
--   \Sigma_{\mu,c}\subset\mathbb R^4\quad\text{is compact}.
--   $$
--
--   This is the compactness consequence of the star-shaped three-sphere component described in Proposition 2.4. Isolating it allows later results about complete regularized dynamics to use the same bounded component.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7. The source derives a star-shaped three-sphere Levi-Civita component and an invariant two-fold antipodal cover below the first critical value.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Compactness of the selected subcritical Levi-Civita component. -/
theorem left_energy_component_compact (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsCompact (leftEnergyComponent μ c) := by sorry

end BirkhoffGlobalSection
