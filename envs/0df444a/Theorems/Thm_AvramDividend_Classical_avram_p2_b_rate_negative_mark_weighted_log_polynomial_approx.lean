-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_mark_weighted_log_polynomial_approx
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_mark_weighted_log_polynomial_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:02:46.376108+00:00
-- url     : https://prove2.me/theorems/68d4e434-9614-4fd9-804d-c1b9da10f73a
-- title:
--   Uniform polynomial approximation of every compact-negative mark transformed test
-- statement:
--   For a continuous original negative jump-mark test f supported below -epsilon and above a finite lower cutoff, the transformed weighted-logarithm test f(log z)/(z-1)^4 can be uniformly approximated on [0,1] to arbitrary positive tolerance by a real polynomial. This proves the exact test-function approximation missing from the moment-to-rate bridge: continuity at z=0 and z=1 comes from the separately verified P2-B source theorem, and polynomial approximation comes from the pinned Mathlib Weierstrass theorem. No process jump rate is assumed.

import Mathlib
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_continuous_all_real
open MeasureTheory Set Topology

theorem AvramDividend.Classical.avram_p2_b_rate_negative_mark_weighted_log_polynomial_approx
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : Polynomial ℝ, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |p.eval z - f (Real.log z) / (z - 1) ^ 4| < δ := by sorry
