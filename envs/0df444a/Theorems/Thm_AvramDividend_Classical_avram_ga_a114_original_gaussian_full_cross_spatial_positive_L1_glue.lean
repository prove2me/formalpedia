-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a114_original_gaussian_full_cross_spatial_positive_L1_glue
-- name    : AvramDividend.Classical.avram_ga_a114_original_gaussian_full_cross_spatial_positive_L1_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:44:26.03548+00:00
-- url     : https://prove2.me/theorems/708df01d-06b6-4457-a33c-1ebea75cb9df
-- title:
--   Original Gaussian true full/cross spatial stopped positive expected L1 closes from absolute full-cell and one-sided single-crossing expected errors
-- statement:
--   Under the exact original stopped Gaussian full/cross spatial residual partition, if the expected absolute full pre-stop source-generator residual sum tends to zero and the expected positive part of the genuinely clipped crossing-cell residual tends to zero, the expected positive part of the total stopped residual tends to zero. The crossing error is used only one-sided, preserving the root assertion and avoiding an unjustified absolute-L1 estimate for the potentially ruin-crossing source.
-- source:
--   Source-faithful root b0 original physical full/cross/post partition ga94 and pointwise ga107 positive split, with Mathlib integral squeeze.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a114_original_gaussian_full_cross_spatial_positive_L1_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U F C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, U m ω = F m ω + C m ω)
    (hUI : ∀ m, Integrable (fun ω => max (U m ω) 0) P)
    (hFI : ∀ m, Integrable (fun ω => |F m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hFT : Tendsto (fun m => ∫ ω, |F m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCT : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (U m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
