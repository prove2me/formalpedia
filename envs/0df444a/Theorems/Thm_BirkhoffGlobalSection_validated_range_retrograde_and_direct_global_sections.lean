-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_validated_range_retrograde_and_direct_global_sections
-- name    : BirkhoffGlobalSection.validated_range_retrograde_and_direct_global_sections
-- status  : Open
-- author  : @Yivy Yu
-- created : 2026-09-12T15:10:57.796996+00:00
-- url     : https://prove2.me/theorems/f1e1e756-cc10-4e08-af7d-0d3a8bfc5d1a
-- title:
--   Validated retrograde and direct global sections
-- statement:
--   Let
--
--   $$
--   0<\mu\leq\frac12,
--   \qquad
--   2.1\leq c\leq2.1+10^{-6}.
--   $$
--
--   The Levi-Civita Hamiltonian flow has a distinguished periodic orbit satisfying the strict Joung--van Koert astronomical-retrograde inequality and a distinguished direct orbit satisfying the corresponding strict negative inequality. Each orbit binds an ordinary disk-like global surface of section on the Levi-Civita component.
--
--   This is the positive-mass restriction of the global-section consequence in Joung--van Koert, Theorems 1.2 and 1.5. Their Proposition 2.2 and proof of Theorem 3.1 supply the strict astronomical sign conditions used here. The paper also includes the degenerate endpoint $\mu=0$; this Lean row omits that endpoint because the uniform local model defines the component inside $D>0$, whereas the second inverse-distance singularity is removable only after specializing to zero mass. Both $c$ endpoints and both binding orbits are retained. The paper's additional action, symmetry, nondegeneracy, knot, self-linking, and index conclusions are not asserted here.
-- source:
--   Joung--van Koert, Theorems 1.2 and 1.5, Proposition 2.2, and the proof of Theorem 3.1, https://arxiv.org/abs/2407.19159v3. The formal row is restricted to positive mass and retains both closed c endpoints.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- The positive-mass part of Joung--van Koert's validated rectangle. Their
Theorems 1.2 and 1.5 give the two binding disks; Proposition 2.2 and the proof
of Theorem 3.1 verify the strict astronomical sign conditions. -/
theorem validated_range_retrograde_and_direct_global_sections (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ γr γd : PeriodicOrbit φ,
      IsAstronomicallyRetrogradeOrbit φ γr ∧
      IsAstronomicallyDirectOrbit φ γd ∧
      DiskLikeGlobalSurfaceOfSection φ γr ∧
      DiskLikeGlobalSurfaceOfSection φ γd := by sorry

end BirkhoffGlobalSection
