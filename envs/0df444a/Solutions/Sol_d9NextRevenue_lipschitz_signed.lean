-- Prove2me | solution 1 for d9NextRevenue_lipschitz_signed
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T14:58:25.210977+00:00
-- url     : https://prove2.me/submissions/b81fc4c7-96b6-4dd5-bb1b-8b6ce22bfbf7

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Theorems.Thm_d9ClippedSeats_increment_bounds
import Theorems.Thm_d9ResidualSeats_mono
import Theorems.Thm_d9ResidualSeats_nonneg
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9NextRevenue_eq_clipped
import Theorems.Thm_signed_affine_clamp_lipschitz
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_lipschitz_signed
    (g : ℝ → ℝ) (p x fare L : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hL : |fare| ≤ L) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |d9NextRevenue g p x fare t - d9NextRevenue g p x fare s| ≤
        L * (t - s) := by
  intro s t hs hst
  rw [d9NextRevenue_eq_clipped g p x fare t hx, d9NextRevenue_eq_clipped g p x fare s hx]
  exact signed_affine_clamp_lipschitz g (d9ClippedSeats p x) (fun s => s - d9ClippedSeats p x s)
    fare L hg hL (fun s t h => (d9ClippedSeats_increment_bounds p x s t hx h).1)
    (fun s t h => d9ResidualSeats_mono p x s t hx h)
    (fun s h => d9ResidualSeats_nonneg p x s hp h) (fun s => by ring) s t hs hst

theorem solution
    (g : ℝ → ℝ) (p x fare L : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hL : |fare| ≤ L) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |d9NextRevenue g p x fare t - d9NextRevenue g p x fare s| ≤
        L * (t - s) := by
  intro s t hs hst
  rw [d9NextRevenue_eq_clipped g p x fare t hx, d9NextRevenue_eq_clipped g p x fare s hx]
  exact signed_affine_clamp_lipschitz g (d9ClippedSeats p x) (fun s => s - d9ClippedSeats p x s)
    fare L hg hL (fun s t h => (d9ClippedSeats_increment_bounds p x s t hx h).1)
    (fun s t h => d9ResidualSeats_mono p x s t hx h)
    (fun s h => d9ResidualSeats_nonneg p x s hp h) (fun s => by ring) s t hs hst


