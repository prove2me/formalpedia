-- Prove2me | solution 1 for d9NextRevenue_lipschitz_threshold
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T14:58:26.122522+00:00
-- url     : https://prove2.me/submissions/bdc79936-c70b-44b8-9001-856fb7d88d99

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Theorems.Thm_d9ClippedSeats_increment_bounds
import Theorems.Thm_d9ResidualSeats_nonneg
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9NextRevenue_eq_clipped
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_lipschitz_threshold
    (g : ℝ → ℝ) (u v x fare s L : ℝ)
    (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) (hL : 0 ≤ L)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|) :
    |d9NextRevenue g u x fare s - d9NextRevenue g v x fare s| ≤
      (|fare| + L) * |u - v| := by
  rw [d9NextRevenue_eq_clipped g u x fare s hx, d9NextRevenue_eq_clipped g v x fare s hx]
  have hc : |d9ClippedSeats u x s - d9ClippedSeats v x s| ≤ |u - v| := by
    unfold d9ClippedSeats
    have h1 : |max 0 (s - u) - max 0 (s - v)| ≤ |(s - u) - (s - v)| := by
      rw [max_comm 0 (s - u), max_comm 0 (s - v)]; exact abs_max_sub_max_le_abs _ _ _
    have h2 : |min x (max 0 (s - u)) - min x (max 0 (s - v))| ≤
        |max 0 (s - u) - max 0 (s - v)| := by
      have := abs_min_sub_min_le_max x (max 0 (s - u)) x (max 0 (s - v))
      simpa using this
    have h3 : |(s - u) - (s - v)| = |u - v| := by
      rw [show (s - u) - (s - v) = -(u - v) by ring, abs_neg]
    linarith
  have hu' := d9ResidualSeats_nonneg u x s hu hs
  have hv' := d9ResidualSeats_nonneg v x s hv hs
  have hg' := hg _ _ hv' hu'
  have e : (s - d9ClippedSeats u x s) - (s - d9ClippedSeats v x s) =
      -(d9ClippedSeats u x s - d9ClippedSeats v x s) := by ring
  rw [e, abs_neg] at hg'
  have key : (fare * d9ClippedSeats u x s + g (s - d9ClippedSeats u x s)) -
      (fare * d9ClippedSeats v x s + g (s - d9ClippedSeats v x s)) =
      fare * (d9ClippedSeats u x s - d9ClippedSeats v x s) +
      (g (s - d9ClippedSeats u x s) - g (s - d9ClippedSeats v x s)) := by ring
  rw [key]
  calc _ ≤ |fare * (d9ClippedSeats u x s - d9ClippedSeats v x s)| +
        |g (s - d9ClippedSeats u x s) - g (s - d9ClippedSeats v x s)| := abs_add_le _ _
    _ ≤ |fare| * |u - v| + L * |u - v| := by
        rw [abs_mul]
        gcongr
        exact hg'.trans (mul_le_mul_of_nonneg_left hc hL)
    _ = (|fare| + L) * |u - v| := by ring

theorem solution
    (g : ℝ → ℝ) (u v x fare s L : ℝ)
    (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) (hL : 0 ≤ L)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|) :
    |d9NextRevenue g u x fare s - d9NextRevenue g v x fare s| ≤
      (|fare| + L) * |u - v| := by
  rw [d9NextRevenue_eq_clipped g u x fare s hx, d9NextRevenue_eq_clipped g v x fare s hx]
  have hc : |d9ClippedSeats u x s - d9ClippedSeats v x s| ≤ |u - v| := by
    unfold d9ClippedSeats
    have h1 : |max 0 (s - u) - max 0 (s - v)| ≤ |(s - u) - (s - v)| := by
      rw [max_comm 0 (s - u), max_comm 0 (s - v)]; exact abs_max_sub_max_le_abs _ _ _
    have h2 : |min x (max 0 (s - u)) - min x (max 0 (s - v))| ≤
        |max 0 (s - u) - max 0 (s - v)| := by
      have := abs_min_sub_min_le_max x (max 0 (s - u)) x (max 0 (s - v))
      simpa using this
    have h3 : |(s - u) - (s - v)| = |u - v| := by
      rw [show (s - u) - (s - v) = -(u - v) by ring, abs_neg]
    linarith
  have hu' := d9ResidualSeats_nonneg u x s hu hs
  have hv' := d9ResidualSeats_nonneg v x s hv hs
  have hg' := hg _ _ hv' hu'
  have e : (s - d9ClippedSeats u x s) - (s - d9ClippedSeats v x s) =
      -(d9ClippedSeats u x s - d9ClippedSeats v x s) := by ring
  rw [e, abs_neg] at hg'
  have key : (fare * d9ClippedSeats u x s + g (s - d9ClippedSeats u x s)) -
      (fare * d9ClippedSeats v x s + g (s - d9ClippedSeats v x s)) =
      fare * (d9ClippedSeats u x s - d9ClippedSeats v x s) +
      (g (s - d9ClippedSeats u x s) - g (s - d9ClippedSeats v x s)) := by ring
  rw [key]
  calc _ ≤ |fare * (d9ClippedSeats u x s - d9ClippedSeats v x s)| +
        |g (s - d9ClippedSeats u x s) - g (s - d9ClippedSeats v x s)| := abs_add_le _ _
    _ ≤ |fare| * |u - v| + L * |u - v| := by
        rw [abs_mul]
        gcongr
        exact hg'.trans (mul_le_mul_of_nonneg_left hc hL)
    _ = (|fare| + L) * |u - v| := by ring


