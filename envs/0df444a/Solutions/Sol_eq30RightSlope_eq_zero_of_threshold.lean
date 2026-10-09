-- Prove2me | solution 1 for eq30RightSlope_eq_zero_of_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:03:04.158017+00:00
-- url     : https://prove2.me/submissions/81faf947-2934-4d19-adaf-c658fd3d4ea5

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30RightSlope
import Definitions.Def_eq30SlopeThreshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (f p x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ k s, eq30SlopeThreshold p x k ≤ s → eq30RightSlope f p x k s = 0 := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro s hs
      simp [eq30RightSlope]
  | one =>
      intro s hs
      have hsx : x 1 ≤ s := by
        simpa [eq30SlopeThreshold] using hs
      simp [eq30RightSlope, not_lt_of_ge hsx]
  | more n ih0 ih1 =>
      intro s hs
      have hbase : x (n + 2) +
          max (p (n + 1)) (eq30SlopeThreshold p x (n + 1)) ≤ s := by
        simpa [eq30SlopeThreshold] using hs
      have hpx : p (n + 1) + x (n + 2) ≤ s := by
        have hmax : p (n + 1) ≤
            max (p (n + 1)) (eq30SlopeThreshold p x (n + 1)) := le_max_left _ _
        linarith
      have hple : p (n + 1) ≤ s := by
        linarith [hpx, hx (n + 2)]
      have hres : eq30SlopeThreshold p x (n + 1) ≤ s - x (n + 2) := by
        have hmax : eq30SlopeThreshold p x (n + 1) ≤
            max (p (n + 1)) (eq30SlopeThreshold p x (n + 1)) := le_max_right _ _
        linarith
      rw [eq30RightSlope, if_neg (not_lt_of_ge hple),
        if_neg (not_lt_of_ge hpx)]
      exact ih1 (s - x (n + 2)) hres
