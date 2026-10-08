-- Prove2me | solution 1 for signed_affine_clamp_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:44:04.813095+00:00
-- url     : https://prove2.me/submissions/6532bb26-28f5-413f-b902-d32d406f7b9d

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NestedSeatAlloc.IntPolicy
theorem solution
    (g c u : ℝ → ℝ) (fare L : ℝ)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hfare : |fare| ≤ L)
    (hc : ∀ s t, s ≤ t → 0 ≤ c t - c s)
    (hu : ∀ s t, s ≤ t → 0 ≤ u t - u s)
    (hu0 : ∀ s, 0 ≤ s → 0 ≤ u s)
    (hsum : ∀ s, c s + u s = s) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |(fare * c t + g (u t)) - (fare * c s + g (u s))| ≤ L * (t - s) := by
  intro s t hs hst
  have hdc : 0 ≤ c t - c s := hc s t hst
  have hdu : 0 ≤ u t - u s := hu s t hst
  have hus : 0 ≤ u s := hu0 s hs
  have hut : 0 ≤ u t := hu0 t (le_trans hs hst)
  have hsplit : (c t - c s) + (u t - u s) = t - s := by
    linarith [hsum t, hsum s]
  calc
    |(fare * c t + g (u t)) - (fare * c s + g (u s))|
        = |fare * (c t - c s) + (g (u t) - g (u s))| := by
          congr 1
          ring
    _ ≤ |fare * (c t - c s)| + |g (u t) - g (u s)| := abs_add_le _ _
    _ ≤ L * (c t - c s) + L * (u t - u s) := by
      apply add_le_add
      · calc
          |fare * (c t - c s)| = |fare| * (c t - c s) := by
            rw [abs_mul, abs_of_nonneg hdc]
          _ ≤ L * (c t - c s) :=
            mul_le_mul_of_nonneg_right hfare hdc
      · calc
          |g (u t) - g (u s)| ≤ L * |u t - u s| :=
            hg (u s) (u t) hus hut
          _ = L * (u t - u s) := by rw [abs_of_nonneg hdu]
    _ = L * (t - s) := by rw [← hsplit]; ring
