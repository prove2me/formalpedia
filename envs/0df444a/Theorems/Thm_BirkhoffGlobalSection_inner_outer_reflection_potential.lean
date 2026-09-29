-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_outer_reflection_potential
-- name    : BirkhoffGlobalSection.inner_outer_reflection_potential
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T23:26:18.815807+00:00
-- url     : https://prove2.me/theorems/ce06017e-e9b1-4e9f-b82f-f232c7a217ea
-- title:
--   Effective-potential inequality under reflection across a primary
-- statement:
--   For a nonnegative mass a and 0<u<1, the effective-potential contribution (a-u)^2/2+a/(1-u) on the inner side is at least (a+u)^2/2+a/(1+u) on the reflected outer side.
-- source:
--   Elementary real inequality obtained from the inverse-distance effective potential associated with Joung--van Koert equation (1.1), https://arxiv.org/abs/2407.19159v3.

import Mathlib

namespace BirkhoffGlobalSection

/-- Reflection across a primary lowers its contribution to the effective potential. -/
theorem inner_outer_reflection_potential (a u : ℝ)
    (ha : 0 ≤ a) (hu : 0 < u) (hu1 : u < 1) :
    (a + u) ^ 2 / 2 + a / (1 + u) ≤
      (a - u) ^ 2 / 2 + a / (1 - u) := by sorry

end BirkhoffGlobalSection
