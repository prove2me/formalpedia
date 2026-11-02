-- Prove2me | solution 1 for gw_constant_08
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T22:54:44.147113+00:00
-- url     : https://prove2.me/submissions/9ec31aab-499d-48aa-9671-9aa160153c1f

import Mathlib

open Real

/-!
# Goemans–Williamson scalar inequality with constant 4/5

`(4/5) * π * (1 - t) ≤ 2 * arccos t` for `t ∈ [-1, 1]`.

No derivative is used. Write `w = arccos t`.

* Case `0 ≤ t ≤ 1`: then `w ∈ [0, π/2]`, `cos w = t`, and `1 - t = 1 - cos w = 2 sin²(w/2)`.
  Since `sin x ≤ x` for `x ≥ 0`, we get `1 - t ≤ w²/2`, hence
  `(4/5) π (1 - t) ≤ (2/5) π w² ≤ 2 w`, the last step because `w ≤ π/2` and `π < 3.15`
  give `(2/5) π w² ≤ (1/5) π² w ≤ 2 w` (`π² < 10`).

* Case `-1 ≤ t < 0`: put `s = -t ∈ [0, 1]`. From `cos (π/2 - s) = sin s ≤ s` and antitony of
  `arccos` we get `arccos s ≤ π/2 - s`, so `arccos t = π - arccos s ≥ π/2 + s = π/2 - t` and
  `2 arccos t ≥ π - 2t`. Finally `π - 2t - (4/5) π (1 - t) = π/5 + t (4π/5 - 2) ≥ 2 - 3π/5 ≥ 0`
  because `t ≥ -1` and `π ≤ 10/3` (from `π < 3.15`).
-/

theorem gw_constant_08 (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    (4 / 5 : ℝ) * Real.pi * (1 - t) ≤ 2 * Real.arccos t := by
  rcases le_or_gt 0 t with ht | ht
  · -- Case `0 ≤ t`: `1 - t = 2 sin²(arccos t / 2) ≤ (arccos t)² / 2`.
    have hw0 : 0 ≤ arccos t := Real.arccos_nonneg t
    have hw1 : arccos t ≤ π / 2 := Real.arccos_le_pi_div_two.2 ht
    have hcos : cos (arccos t) = t := Real.cos_arccos h1 h2
    have hone : 1 - t = 2 * sin (arccos t / 2) ^ 2 := by
      have h := Real.cos_two_mul_eq_one_sub (x := arccos t / 2)
      have h2' : 2 * (arccos t / 2) = arccos t := by ring
      rw [h2'] at h
      linarith
    have hsinnn : 0 ≤ sin (arccos t / 2) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [Real.pi_pos, hw0]
    have hsinle : sin (arccos t / 2) ≤ arccos t / 2 := Real.sin_le (by linarith)
    have h1mt : 1 - t ≤ arccos t ^ 2 / 2 := by
      rw [hone]
      nlinarith
    have hpile : π ≤ 3.15 := Real.pi_lt_d2.le
    nlinarith [Real.pi_pos, hw0, hw1, hpile, h1mt]
  · -- Case `t < 0`: `arccos(-s) = π - arccos s` with `arccos s ≤ π/2 - s`.
    set s := -t with hsdef
    have hs0 : 0 ≤ s := by linarith
    have hs1 : s ≤ 1 := by linarith
    have harcs : arccos s ≤ π / 2 - s := by
      have hy0 : 0 ≤ π / 2 - s := by linarith [Real.pi_gt_d2]
      have hy1 : π / 2 - s ≤ π := by linarith [Real.pi_pos]
      rw [← Real.arccos_cos hy0 hy1]
      refine Real.arccos_le_arccos ?_
      rw [Real.cos_pi_div_two_sub]
      exact Real.sin_le hs0
    have ht_eq : t = -s := by linarith
    have ht' : arccos t = π - arccos s := by
      rw [ht_eq]
      exact Real.arccos_neg s
    have hpi_le : π ≤ 10 / 3 := by linarith [Real.pi_lt_d2]
    nlinarith [ht', ht_eq, harcs, hpi_le, Real.pi_gt_d2, Real.pi_pos, hs0, hs1]

/-- The GW scalar inequality with comfortable constant, packaged as the platform solution. -/
theorem solution (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    (4 / 5 : ℝ) * Real.pi * (1 - t) ≤ 2 * Real.arccos t :=
  gw_constant_08 t h1 h2

#print axioms solution
