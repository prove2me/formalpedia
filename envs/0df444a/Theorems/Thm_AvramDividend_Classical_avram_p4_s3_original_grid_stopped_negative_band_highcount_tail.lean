-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_grid_stopped_negative_band_highcount_tail
-- name    : AvramDividend.Classical.avram_p4_s3_original_grid_stopped_negative_band_highcount_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:06:33.34961+00:00
-- url     : https://prove2.me/theorems/2be99388-c1a4-4116-bdb5-1d83322dc528
-- title:
--   Uniform quadratic tail bound for original negative-band counts at bounded grid-selected clocks
-- statement:
--   For a measurable integer-selected original stopping grid bounded by T, the original number of negative-band jumps is square integrable. At every positive integer threshold m, its physical probability of m or more jumps is at most (r+r²)/m², r=Tν(B). This supplies quantitative tightness and high-count truncation for stopped predictable finite-band compensation on the actual process.
-- source:
--   Accepted exact original grid count measurability 4926eb4c-28dc-4528-9825-578fd279f92f and square moment budget 0cb80e25-f18f-4e12-af48-9dddb5f8be34, followed by real L2 Markov/Chebyshev probability bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_grid_stopped_negative_band_highcount_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (tick : Ω → ℕ) (htick : Measurable tick)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ ω, grid (tick ω) ≤ T)
    (m : ℕ) (hm : 0 < m) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ grid (tick ω) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | m ≤ K ω} ≤ (r ^ 2 + r) / (m : ℝ) ^ 2 := by sorry
