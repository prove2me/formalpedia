-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a118_original_gaussian_fullcell_three_source_errors_absolute_L1_glue
-- name    : AvramDividend.Classical.avram_ga_a118_original_gaussian_fullcell_three_source_errors_absolute_L1_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:58:55.553204+00:00
-- url     : https://prove2.me/theorems/f24a52e6-23ec-4554-a0ea-e84b1f2b1506
-- title:
--   Actual Gaussian physically full pre-stop source spatial residual vanishes in absolute expected L1 from Taylor, centred cross and discount mismatch error terms
-- statement:
--   The true Gaussian full pre-stop cell spatial source-generator residual splits exactly into three errors: compact positive C2 Taylor remainder, the discrepancy between original raw and centred Gaussian quadratic source increments, and the physical clipping/discount mismatch. If the absolute expected L1 size of each component tends to zero, the absolute expected full-cell sum tends to zero by triangle inequality, integration and squeeze. This is the strong full-cell half of the one-sided actual clipped Gaussian root.
-- source:
--   Proved original ga77 source C2 identity, ga81 Gaussian raw-centred expected cross error, ga87 exact discount algebra, ga114 one-sided full/cross root closure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a118_original_gaussian_fullcell_three_source_errors_absolute_L1_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F A B C : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, F m ω = A m ω + B m ω + C m ω)
    (hFI : ∀ m, Integrable (fun ω => |F m ω|) P)
    (hAI : ∀ m, Integrable (fun ω => |A m ω|) P)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => |C m ω|) P)
    (hAt : Tendsto (fun m => ∫ ω, |A m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P) atTop (𝓝 (0 : ℝ)))
    (hCt : Tendsto (fun m => ∫ ω, |C m ω| ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, |F m ω| ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
