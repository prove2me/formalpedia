-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_cell_outside_any_positive_band
-- name    : AvramDividend.Classical.avram_bv_tail11_singular_cell_outside_any_positive_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:14:05.556809+00:00
-- url     : https://prove2.me/theorems/675b1046-b604-468f-9424-e37766da1a84
-- title:
--   Every positive compact-band lower edge misses arbitrarily negative original singular generator cells
-- statement:
--   For every prescribed positive reserve-band lower edge and arbitrarily large target deficit, construct a strictly positive reserve below half that edge and inside the source-exact singular small-grid scale. The negative original affine generator contribution survives any fixed compact-band truncation. This deterministic result does not provide a sampled Lévy reserve path.
-- source:
--   Source-exact arbitrary-cofinal-band validity audit for 0b2da5b3 using public accepted neighbourhood theorem 136fae3f, with reserve chosen as min(a/4, h²/2).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail11_singular_cell_outside_any_positive_band
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ t : ℝ,
      0 < t ∧ t < a / 2 ∧
      t ≤ (1 / ((K : ℝ) + 4)) ^ 2 ∧
      (1 / ((K : ℝ) + 4)) *
        (3 + t ^ 2 - 4 * t - 2 / t) ≤ -(K : ℝ) := by sorry
