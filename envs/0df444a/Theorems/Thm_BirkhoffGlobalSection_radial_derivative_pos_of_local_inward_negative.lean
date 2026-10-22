-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_derivative_pos_of_local_inward_negative
-- name    : BirkhoffGlobalSection.radial_derivative_pos_of_local_inward_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:12:26.303177+00:00
-- url     : https://prove2.me/theorems/1e79de55-1ec6-4b12-8f91-dfe0ecb576ae
-- title:
--   Radial derivative pos of local inward negative
-- statement:
--   For a twice differentiable defining function at a nonzero boundary point, local inward radial negativity and positive Hessian on nonzero kernel directions imply a strictly positive radial derivative. The ambient space may be any real normed space.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 8 of the Proved theorem BirkhoffGlobalSection.radial_characteristic_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_radial_characteristic_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_radial_derivative_pos_of_local_inward_negative

theorem BirkhoffGlobalSection.radial_derivative_pos_of_local_inward_negative :
∀ {E : Type u_radial_derivative_pos_of_local_inward_negative}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v),
    0 < fderiv ℝ F s s := by sorry
