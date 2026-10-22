-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
-- name    : BirkhoffGlobalSection.left_energy_component_geometry
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:08:41.594325+00:00
-- url     : https://prove2.me/theorems/e0c014c9-ac15-4ff4-a399-d6a047b4123c
-- title:
--   Geometry of the subcritical Levi-Civita component
-- statement:
--   Let $0<\mu<1$ and $-c<h_1(\mu)$. Then the selected Levi-Civita component $\Sigma_{\mu,c}$ is compact, $K_{\mu,c}$ is $C^\infty$ there with nonzero derivative at every point, and the antipodal map preserves the component and acts freely. The component admits a homeomorphism to the round unit three-sphere that intertwines the antipodal maps:
--
--   $$
--   e:\Sigma_{\mu,c}\cong S^3,
--   \qquad e(-s)=-e(s).
--   $$
--
--   This is the equivariant sphere model underlying the two-to-one Levi-Civita cover in Joung--van Koert Proposition 2.4. It makes compactness, regularity, topology, and the deck action explicit instead of folding them into the word “component.”
-- source:
--   Joung--van Koert, Proposition 2.4, https://arxiv.org/abs/2407.19159v3. The row records compactness, regularity, the sphere model, and the free invariant deck action used by the formal quotient.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- Below the first critical value, the selected Levi-Civita component is a
compact regular hypersurface with an antipodally equivariant sphere model. -/
theorem left_energy_component_geometry (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsCompact (leftEnergyComponent μ c) ∧
    (∀ s ∈ leftEnergyComponent μ c,
      ContDiffAt ℝ ∞ (leviCivitaHamiltonian μ c) s ∧
      fderiv ℝ (leviCivitaHamiltonian μ c) s ≠ 0) ∧
    IsAntipodallyInvariantComponent μ c ∧
    IsAntipodallyFreeComponent μ c ∧
    ∃ e : LeftEnergyState μ c ≃ₜ
        {x : Phase // x ∈ unitThreeSphere},
      IsAntipodallyEquivariantSphereHomeomorph e := by sorry

end BirkhoffGlobalSection
