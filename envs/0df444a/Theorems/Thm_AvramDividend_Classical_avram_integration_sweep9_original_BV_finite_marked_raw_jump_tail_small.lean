-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_BV_finite_marked_raw_jump_tail_small
-- name    : AvramDividend.Classical.avram_integration_sweep9_original_BV_finite_marked_raw_jump_tail_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:46:24.758981+00:00
-- url     : https://prove2.me/theorems/afacd8f9-8a1a-4f94-ba49-7be1868d7026
-- title:
--   Original BV finite marked-jump cutoff with arbitrarily small residual jump series
-- statement:
--   For almost every sample path of the original bounded-variation spectrally negative Levy source, every positive tolerance admits a finite set of marked jump times outside which the signed real negative-left-jump series on a fixed positive horizon has absolute sum below that tolerance.
-- source:
--   Original physical BV raw negative jump summability f0ec726b and finite-complement identity Summable.sum_add_tsum_compl. Supplies the missing finite marked cutoff for uniform stopped-grid tail control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep9_original_BV_finite_marked_raw_jump_tail_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ marked : Finset ℝ≥0,
        |∑' t : {t : ℝ≥0 // t ∉ marked},
          if 0 < (t : ℝ≥0) ∧ (t : ℝ≥0) ≤ T then
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) t - X.X t ω
          else 0| < ε := by sorry
