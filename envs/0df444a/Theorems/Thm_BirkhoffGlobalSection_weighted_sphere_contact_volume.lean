-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_contact_volume
-- name    : BirkhoffGlobalSection.weighted_sphere_contact_volume
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:57:56.112979+00:00
-- url     : https://prove2.me/theorems/a59be048-25c5-4ef6-8113-741e4e7e3d58
-- title:
--   Weighted sphere contact volume
-- statement:
--   A positive differentiable sphere weight admits three tangent vectors on which its contact volume evaluates positively, with the stated exterior-derivative and orientation convention.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_weighted_sphere_contact_geometry.lean:74. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_sphere_contact_volume (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u) :
    let d : Phase → Phase → ℝ := fun v w =>
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w
    ∃ r v w : Phase,
      (u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0) ∧
      (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      (u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) ∧
      0 < f u * phaseRadialContact u r * d v w -
        f u * phaseRadialContact u v * d r w +
        f u * phaseRadialContact u w * d r v := by sorry
