-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_discounted_uniform_generator_cell
-- name    : AvramDividend.Classical.avram_bv_tail12_original_discounted_uniform_generator_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:28:45.475479+00:00
-- url     : https://prove2.me/theorems/f85331a1-f95f-40fa-9eaa-2b8c88624039
-- title:
--   Discounted original singular generator cell on the uniform physical grid
-- statement:
--   For a genuine bounded-variation spectrally negative Levy generator with the singular negative jump density and zero characteristic drift, the discounted cell on the exact uniform T over n plus two mesh is at most minus K whenever its positive reserve is sufficiently small and the discounted mesh width exceeds the reciprocal K plus four threshold. This records the sign and discount factors appearing literally in the canonical stopped B sum.
-- source:
--   Direct corollary of Proved public 3bceec57 original-generator uniform near-zero, with multiplication by a nonpositive generator deficit. Bridges accepted generator bounds to exact discounted uniform-grid B cells in canonical 0b2da5b3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_generator_uniform_near_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail12_original_discounted_uniform_generator_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0) (K n : ℕ) (T t y : ℝ)
    (hy : 0 < y) (hy1 : y < 1)
    (hy_small : y ≤ (1 / ((K : ℝ) + 4)) ^ 4)
    (hweight : 1 / ((K : ℝ) + 4) ≤
      Real.exp (-t) * (T / ((n : ℝ) + 2))) :
    Real.exp (-t) *
      (X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) y -
        (1 + y)) * (T / ((n : ℝ) + 2)) ≤ -(K : ℝ) := by sorry
