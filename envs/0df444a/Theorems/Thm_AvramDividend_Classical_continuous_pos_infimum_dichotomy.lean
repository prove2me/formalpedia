-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_pos_infimum_dichotomy
-- name    : AvramDividend.Classical.continuous_pos_infimum_dichotomy
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T20:13:43.894393+00:00
-- url     : https://prove2.me/theorems/dfc97c02-0022-4a79-87c5-3d90da6e2d3a
-- title:
--   A continuous coercive function on (0,∞) attains its infimum or its right liminf is minimal
-- statement:
--   Let f be continuous on (0,∞) and tend to +∞ at +∞. Then either f has a global minimizer at some positive point, or the extended-real liminf of f as x↓0 is no larger than f(x) for every x>0. This is the pure real-analysis dichotomy needed to turn the scale-function derivative regularity and growth facts into Lemma 2(i).
-- source:
--   Elementary real analysis decomposition of Avram–Palmowski–Pistorius Lemma 2(i).

import Mathlib

open Filter Set Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem continuous_pos_infimum_dichotomy (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Ioi 0))
    (htop : Filter.Tendsto f Filter.atTop Filter.atTop) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x) ∨
      ∀ x : ℝ, 0 < x →
        Filter.liminf (fun y => ((f y : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) ≤
          ((f x : ℝ) : EReal) := by sorry

end AvramDividend.Classical
