-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_smooth_weighted_sphere_contact
-- name    : BirkhoffGlobalSection.smooth_weighted_sphere_contact
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-03T23:02:46.01295+00:00
-- url     : https://prove2.me/theorems/6d23d4ee-c117-4b60-82ff-bdb365356900
-- title:
--   Smooth weighted sphere contact
-- statement:
--   At a sphere point with positive weight, the weighted radial contact form is nonzero. If the weight is differentiable there, its exterior derivative is nondegenerate on the contact kernel.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_weighted_sphere_contact_geometry.lean:53. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_nondegenerate
open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.smooth_weighted_sphere_contact (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) :
    (∃ r : Phase,
      u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0 ∧
      f u * phaseRadialContact u r ≠ 0) ∧
    (DifferentiableAt ℝ f u → ∀ v : Phase,
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0 →
      f u * phaseRadialContact u v = 0 →
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        f u * phaseRadialContact u w = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
          fderiv ℝ (fun x => f x * phaseRadialContact x v) u w = 0) → v = 0) := by sorry
