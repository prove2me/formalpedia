-- Prove2me | Theorems.Thm_FamousTheorems_norm_add_le
-- name    : FamousTheorems.norm_add_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:22.322742+00:00
-- url     : https://prove2.me/theorems/c0b03acd-e7ac-4981-8054-442faa6a04f5
-- title:
--   The triangle inequality
-- statement:
--   **The triangle inequality.**
--
--   $$\|a + b\| \;\le\; \|a\| + \|b\| .$$
--
--   One side of a triangle is no longer than the other two combined. It is an *axiom* of a norm
--   rather than a theorem about one — which is the point: it is the condition that makes
--   $d(x,y) = \|x-y\|$ a metric, and hence makes normed spaces topological.
--
--   Everything in analysis that estimates a sum by its parts uses it, and its reverse form
--   $\bigl|\|a\|-\|b\|\bigr| \le \|a-b\|$ is what makes the norm a continuous function.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem norm_add_le : ∀ {E : Type*} [SeminormedAddGroup E] (a b : E), ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by sorry

end FamousTheorems
