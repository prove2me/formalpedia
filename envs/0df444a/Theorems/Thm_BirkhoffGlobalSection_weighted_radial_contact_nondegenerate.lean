-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_nondegenerate
-- name    : BirkhoffGlobalSection.weighted_radial_contact_nondegenerate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:52:01.147548+00:00
-- url     : https://prove2.me/theorems/1c4c557c-44e4-4648-9e4f-8cd824a6f11c
-- title:
--   Weighted radial contact nondegenerate
-- statement:
--   A positive constant weight times the radial contact form on a sphere tangent space is nonzero and has nondegenerate exterior pairing on its contact kernel, even with the displayed arbitrary coefficient function L.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_weighted_sphere_contact_geometry.lean:6. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.weighted_radial_contact_nondegenerate (u : Phase) (hu : u ∈ unitThreeSphere)
    (f : ℝ) (hf : 0 < f) (L : Phase → ℝ) :
    (∃ r : Phase,
      u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0 ∧
      f * phaseRadialContact u r ≠ 0) ∧
    (∀ v : Phase,
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0 →
      f * phaseRadialContact u v = 0 →
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        f * phaseRadialContact u w = 0 →
        L v * phaseRadialContact u w - L w * phaseRadialContact u v -
          f * phaseSymplecticForm v w = 0) → v = 0) := by sorry
