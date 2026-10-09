-- Prove2me | solution 1 for eq30NextPayoff_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:27:07.483471+00:00
-- url     : https://prove2.me/submissions/1625f8cc-35cd-46d7-93c1-cbc0caefd6c9

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
import Definitions.Def_eq30ClippedSeats
import Theorems.Thm_eq30ClippedSeats_increment_bounds
import Theorems.Thm_eq30ResidualSeats_mono
import Theorems.Thm_eq30NextPayoff_eq_clipped
import Theorems.Thm_eq30_affine_clamp_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
theorem solution
    (g : ℝ → ℝ) (p x fare L : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hfare0 : 0 ≤ fare) (hfareL : fare ≤ L) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |eq30NextPayoff g p x fare t - eq30NextPayoff g p x fare s| ≤
        L * (t - s) := by
  let c : ℝ → ℝ := fun z => eq30ClippedSeats p x z
  let u : ℝ → ℝ := fun z => z - c z
  have hc : ∀ s t, s ≤ t → 0 ≤ c t - c s := by
    intro s t hst
    simpa [c] using
      (eq30ClippedSeats_increment_bounds p x s t hx hst).1
  have hu : ∀ s t, s ≤ t → 0 ≤ u t - u s := by
    intro s t hst
    simpa [u, c] using eq30ResidualSeats_mono p x s t hx hst
  have hu0 : ∀ s, 0 ≤ s → 0 ≤ u s := by
    intro s hs
    dsimp [u, c]
    have hmax : max 0 (s - p) ≤ s := max_le_iff.mpr ⟨hs, by linarith⟩
    have hclip : eq30ClippedSeats p x s ≤ max 0 (s - p) := min_le_right _ _
    linarith
  have hsum : ∀ s, c s + u s = s := by
    intro s
    dsimp [u]
    ring
  have hmain := eq30_affine_clamp_lipschitz g c u fare L
    hg hfare0 hfareL hc hu hu0 hsum
  intro s t hs hst
  rw [eq30NextPayoff_eq_clipped g p x fare t hx,
    eq30NextPayoff_eq_clipped g p x fare s hx]
  simpa [c, u] using hmain s t hs hst
