-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_local_inward_negative_derivative_nonnegative
-- name    : BirkhoffGlobalSection.local_inward_negative_derivative_nonnegative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:26.876516+00:00
-- url     : https://prove2.me/theorems/8461db23-bf53-4694-916e-15aa7882e123
-- title:
--   Local inward negative derivative nonnegative
-- statement:
--   A differentiable real function vanishing at one and strictly negative on a left interval ending at one has nonnegative derivative at one.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 7 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.local_inward_negative_derivative_nonnegative :
∀ (f : ℝ → ℝ) (d ε : ℝ)
    (hε : 0 < ε) (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0),
    0 ≤ d := by sorry
