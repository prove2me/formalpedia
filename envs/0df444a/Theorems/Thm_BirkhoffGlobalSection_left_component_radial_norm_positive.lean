-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_radial_norm_positive
-- name    : BirkhoffGlobalSection.left_component_radial_norm_positive
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T09:57:49.726238+00:00
-- url     : https://prove2.me/theorems/340fa744-6eeb-430e-b636-6065971b8837
-- title:
--   The left component avoids the origin of regularized phase space
-- statement:
--   Every state on the selected subcritical regularized energy component has strictly positive squared Euclidean norm in its four phase coordinates. Equivalently, the component avoids the origin, so radial projection is defined everywhere on it. This follows from the positive collision momentum at the left primary for $0<\mu<1$.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, equation (2.2), regularized left-primary collision state.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_component_radial_norm_positive (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ leftEnergyComponent μ c,
      0 < zNormSq s + wNormSq s := by sorry

end BirkhoffGlobalSection
