-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_time_change_shear_derivative
-- name    : BirkhoffGlobalSection.positive_time_change_shear_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:13:08.144185+00:00
-- url     : https://prove2.me/theorems/65b64fd3-53ce-4166-bb12-e459d3406a73
-- title:
--   Positive time change shear derivative
-- statement:
--   For a positive differentiable rate satisfying the stated logarithmic derivative equation, the integral-defined shear coefficient satisfies its inhomogeneous first-order derivative equation.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 2 of the Proved theorem BirkhoffGlobalSection.positive_time_change_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_positive_time_change_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.positive_time_change_shear_derivative :
∀ (r k l : ℝ → ℝ) (hr : Continuous r) (hk : Continuous k)
    (hpos : ∀ t, 0 < r t) (hdr : ∀ t, HasDerivAt r (r t * l t) t),
    let η : ℝ → ℝ := fun t => r t * ∫ s in (0 : ℝ)..t, k s / r s
    η 0 = 0 ∧ ∀ t, HasDerivAt η (k t + η t * l t) t := by sorry
