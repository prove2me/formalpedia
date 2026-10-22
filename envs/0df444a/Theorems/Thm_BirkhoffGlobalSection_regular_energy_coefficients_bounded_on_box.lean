-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_regular_energy_coefficients_bounded_on_box
-- name    : BirkhoffGlobalSection.regular_energy_coefficients_bounded_on_box
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T08:17:43.06765+00:00
-- url     : https://prove2.me/theorems/19ab93a5-5a10-484e-8adb-96bc53724d79
-- title:
--   Coefficient bounds away from collision
-- statement:
--   When both Levi-Civita position coordinates lie in a fixed box and the distance from the second collision is bounded below by $\delta>0$, all three position-dependent coefficients of the energy equation—its two momentum-linear coefficients and its constant term—are uniformly bounded in absolute value. The bound depends only on $\mu,c,R_z,\delta$.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, equation (2.2); elementary coercivity estimate.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem regular_energy_coefficients_bounded_on_box
    (μ c Rz δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ regularEnergyLocus μ c,
      |s 0| ≤ Rz → |s 1| ≤ Rz →
      δ ≤ Real.sqrt (secondCollisionDistanceSq s) →
      |-(2 * zNormSq s + μ) * s 1| ≤ M ∧
      |(2 * zNormSq s - μ) * s 0| ≤ M ∧
      |c * zNormSq s - (1 - μ) / 2 -
        μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)| ≤ M := by sorry

end BirkhoffGlobalSection
