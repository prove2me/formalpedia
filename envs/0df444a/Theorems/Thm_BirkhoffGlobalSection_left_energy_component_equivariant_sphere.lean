-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_equivariant_sphere
-- name    : BirkhoffGlobalSection.left_energy_component_equivariant_sphere
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T16:58:10.396169+00:00
-- url     : https://prove2.me/theorems/e76cf94a-6d83-49a4-8180-82f8f4545181
-- title:
--   Antipodally equivariant sphere model for the component
-- statement:
--   Let $0<\mu<1$ and let the Jacobi energy $-c$ lie strictly below the first critical value. Write $\Sigma_{\mu,c}$ for the connected component of the regular Levi-Civita energy level based at the regularized collision over the left primary. There is a homeomorphism to the round three-sphere that intertwines the antipodal involution:
--
--   $$
--   \exists\,e:\Sigma_{\mu,c}\xrightarrow{\simeq}S^3,\qquad e(-s)=-e(s).
--   $$
--
--   The source proves that the component is star-shaped, hence a three-sphere, and is invariant under $(z,w)\mapsto(-z,-w)$. Radial normalization is antipodally equivariant; this is the reusable sphere-model clause needed for the two-fold cover.
--
--   **Formalization Note.** The target requests a homeomorphism of the explicit Levi-Civita component, not a smooth atlas on the quotient.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7. The source derives a star-shaped three-sphere Levi-Civita component and an invariant two-fold antipodal cover below the first critical value.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The star-shaped subcritical component has an antipodally equivariant
radial model by the round three-sphere. -/
theorem left_energy_component_equivariant_sphere (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ e : LeftEnergyState μ c ≃ₜ {x : Phase // x ∈ unitThreeSphere},
      IsAntipodallyEquivariantSphereHomeomorph e := by sorry

end BirkhoffGlobalSection
