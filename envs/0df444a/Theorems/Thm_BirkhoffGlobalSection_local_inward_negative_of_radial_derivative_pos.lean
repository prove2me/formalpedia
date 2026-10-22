-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_local_inward_negative_of_radial_derivative_pos
-- name    : BirkhoffGlobalSection.local_inward_negative_of_radial_derivative_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:46.77101+00:00
-- url     : https://prove2.me/theorems/37611aa9-8d05-47f4-be1b-280d134865de
-- title:
--   Local inward negative of radial derivative pos
-- statement:
--   A differentiable real-valued function vanishing at a point with positive radial derivative is strictly negative along a sufficiently short inward radial segment from that point.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 10 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_local_inward_negative_of_radial_derivative_pos

theorem BirkhoffGlobalSection.local_inward_negative_of_radial_derivative_pos :
∀ {E : Type u_local_inward_negative_of_radial_derivative_pos}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : DifferentiableAt ℝ F s) (hzero : F s = 0)
    (hrad : 0 < fderiv ℝ F s s),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0 := by sorry
