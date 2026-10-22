-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_regular
-- name    : BirkhoffGlobalSection.left_energy_component_regular
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T16:58:05.416015+00:00
-- url     : https://prove2.me/theorems/868c235a-0ef4-4ca8-ad49-366e5be535b9
-- title:
--   Regularity of the subcritical Levi-Civita energy level
-- statement:
--   Let $0<\mu<1$ and let the Jacobi energy $-c$ lie strictly below the first critical value. Write $\Sigma_{\mu,c}$ for the connected component of the regular Levi-Civita energy level based at the regularized collision over the left primary. At every state on this component, the derivative of the regularized Hamiltonian $K_{\mu,c}$ is nonzero:
--
--   $$
--   \forall s\in\Sigma_{\mu,c},\qquad dK_{\mu,c}(s)\ne0.
--   $$
--
--   This records the regular-hypersurface assertion implicit in the subcritical energy level and its star-shaped sphere description. Smoothness away from the second collision is available as a separate proved theorem.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7. The source derives a star-shaped three-sphere Levi-Civita component and an invariant two-fold antipodal cover below the first critical value.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The subcritical Levi-Civita energy component contains no stationary
point of the regularized Hamiltonian. -/
theorem left_energy_component_regular (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ leftEnergyComponent μ c,
      fderiv ℝ (leviCivitaHamiltonian μ c) s ≠ 0 := by sorry

end BirkhoffGlobalSection
