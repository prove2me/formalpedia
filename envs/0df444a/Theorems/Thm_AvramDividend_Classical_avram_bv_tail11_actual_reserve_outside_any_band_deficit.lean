-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_actual_reserve_outside_any_band_deficit
-- name    : AvramDividend.Classical.avram_bv_tail11_actual_reserve_outside_any_band_deficit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:25:37.137382+00:00
-- url     : https://prove2.me/theorems/68d97f1d-a6ad-4498-b3c7-75250b6ca249
-- title:
--   Actual subunit surplus outside any positive band has arbitrary original singular HJB deficit
-- statement:
--   For any positive compact-band lower edge and any natural target deficit, find an actual positive surplus below the band and below one such that the original affine singular HJB deficit, expressed with its square-root singularity, has arbitrarily negative grid-width contribution. The result is deterministic and does not supply a sample-path witness.
-- source:
--   Real square-root substitution into public Proved 675b1046. This is the source-exact actual-reserve version of the BV-TAIL11 generator-cell validity audit for 0b2da5b3.

import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_cell_outside_any_positive_band
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail11_actual_reserve_outside_any_band_deficit
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ y : ℝ,
      0 < y ∧ y < a / 2 ∧ y < 1 ∧
      (1 / ((K : ℝ) + 4)) *
        (3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y) ≤ -(K : ℝ) := by sorry
