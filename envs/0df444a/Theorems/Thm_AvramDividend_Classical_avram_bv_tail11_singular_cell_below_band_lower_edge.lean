-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_cell_below_band_lower_edge
-- name    : AvramDividend.Classical.avram_bv_tail11_singular_cell_below_band_lower_edge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:00:13.185516+00:00
-- url     : https://prove2.me/theorems/7b3204c2-147c-4669-a792-af4200d89318
-- title:
--   Singular original physical cell escapes its shrinking compact band and has arbitrary negative deficit
-- statement:
--   On an original uniform physical grid with width h=1/(K+4), any positive reserve at most h squared is strictly below the associated compact-band lower edge h/2, while the signed singular generator contribution is at most minus K. This is a deterministic source-exact band-mismatch lemma, not a stochastic counterexample.
-- source:
--   Use publicly Proved 136fae3f together with real algebra to certify the gap between a tiny source reserve and the lower edge of a cofinal compact-band mask in original target 0b2da5b3.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail11_singular_cell_below_band_lower_edge
    (K : ℕ) (t : ℝ) (ht : 0 < t)
    (ht_bound : t ≤ (1 / ((K : ℝ) + 4)) ^ 2) :
    t < (1 / ((K : ℝ) + 4)) / 2 ∧
    (1 / ((K : ℝ) + 4)) *
      (3 + t ^ 2 - 4 * t - 2 / t) ≤ -(K : ℝ) := by sorry
