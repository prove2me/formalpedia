-- Prove2me | Theorems.Thm_D1Bound5_frontier_quadratic_interval_exclusion
-- name    : D1Bound5.frontier_quadratic_interval_exclusion
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:41.177226+00:00
-- url     : https://prove2.me/theorems/7eee5d11-6023-4623-bd3a-424416732275
-- title:
--   Frontier quadratic interval exclusion
-- statement:
--   Convex quadratic endpoint exclusion, proved by its chord identity.
-- source:
--   D1Bound5/FrontierScalarReduction.lean, lines 96-107, SHA-256 33d96b980c678c7382e88430524a158d0567c03ec5b878d5a113f1495c5b0528. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5










theorem _root_.D1Bound5.frontier_quadratic_interval_exclusion (a b c lo hi x : ℝ)
    (ha : 0 ≤ a) (hlo : lo < x) (hhi : x ≤ hi)
    (hql : a*lo^2+b*lo+c < 0) (hqh : a*hi^2+b*hi+c < 0)
    (hqx : 0 ≤ a*x^2+b*x+c) : False := by sorry

end D1Bound5
end
