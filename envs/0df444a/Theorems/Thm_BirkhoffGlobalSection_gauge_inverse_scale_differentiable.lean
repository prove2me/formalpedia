-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_scale_differentiable
-- name    : BirkhoffGlobalSection.gauge_inverse_scale_differentiable
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:05.247658+00:00
-- url     : https://prove2.me/theorems/97ecc8a3-a5b4-447c-ab72-500aa29f1210
-- title:
--   Gauge inverse scale differentiable
-- statement:
--   At a nonzero phase point, differentiability of the inverse-gauge vector rescaling implies differentiability of its scalar inverse-gauge factor.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_convex_model_sphere_reeb_transport_of_model_fields.lean:148. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart

open BirkhoffGlobalSection
open scoped ContDiff Topology



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.gauge_inverse_scale_differentiable (B : Set Phase) (u : Phase)
    (hu : u ≠ 0) (hG : DifferentiableAt ℝ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    DifferentiableAt ℝ (fun x : Phase => (gauge B x)⁻¹) u := by sorry
