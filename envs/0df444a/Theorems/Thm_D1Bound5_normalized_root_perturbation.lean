-- Prove2me | Theorems.Thm_D1Bound5_normalized_root_perturbation
-- name    : D1Bound5.normalized_root_perturbation
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:48.938531+00:00
-- url     : https://prove2.me/theorems/1a298129-340b-499b-aa7e-ee02ba94a474
-- title:
--   Normalized root perturbation
-- statement:
--   An elementary root estimate. No analytic branch or power series is needed: the sign is specified by the nonnegative real part.
-- source:
--   D1Bound5/RootPerturbation.lean, lines 8-33, SHA-256 7aaad87d1ed5a59f43b252455f1ebbb4d1f05aeee8eed1621908f38851f48649. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.normalized_root_perturbation (q : ℂ) (c rho : ℝ)
    (hc : 0 ≤ c) (hrho : 0 < rho) (hgap : rho < 1-c^2)
    (hRe : 0 ≤ q.re) (hq : ‖q^2-1‖ ≤ rho) :
    (1+c)*‖q-1‖ < rho := by sorry



end D1Bound5
end
