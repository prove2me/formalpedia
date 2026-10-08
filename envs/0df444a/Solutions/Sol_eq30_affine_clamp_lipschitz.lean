-- Prove2me | solution 1 for eq30_affine_clamp_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T10:14:23.358306+00:00
-- url     : https://prove2.me/submissions/be537bae-640b-4764-b258-b57b2d544d5d

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (g c u : ℝ → ℝ) (fare L : ℝ)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hfare0 : 0 ≤ fare) (hfareL : fare ≤ L)
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
  have hL : 0 ≤ L := le_trans hfare0 hfareL
  calc
    |(fare * c t + g (u t)) - (fare * c s + g (u s))|
        = |fare * (c t - c s) + (g (u t) - g (u s))| := by
      congr 1
      ring
    _ ≤ |fare * (c t - c s)| + |g (u t) - g (u s)| := abs_add_le _ _
    _ ≤ fare * (c t - c s) + L * (u t - u s) := by
      apply add_le_add
      · rw [abs_of_nonneg (mul_nonneg hfare0 hdc)]
      · calc
          |g (u t) - g (u s)| ≤ L * |u t - u s| := hg (u s) (u t) hus hut
          _ = L * (u t - u s) := by rw [abs_of_nonneg hdu]
    _ ≤ L * ((c t - c s) + (u t - u s)) := by
      have hgap : 0 ≤ L - fare := sub_nonneg.mpr hfareL
      have hprod : 0 ≤ (L - fare) * (c t - c s) := mul_nonneg hgap hdc
      have hprod' : 0 ≤ L * (u t - u s) := mul_nonneg hL hdu
      nlinarith
    _ = L * (t - s) := by rw [hsplit]
