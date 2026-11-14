-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a125_original_gaussian_masked_full_cross_positive_expected_L1_glue
-- name    : AvramDividend.Classical.avram_ga_a125_original_gaussian_masked_full_cross_positive_expected_L1_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:12:53.046384+00:00
-- url     : https://prove2.me/theorems/860590d9-5416-41ba-a7b0-352c91792bda
-- title:
--   Actual Gaussian masked stopped spatial positive expected L1 vanishes from full-cell absolute and true crossing-cell one-sided expected errors
-- statement:
--   For any source-exact full versus truly clipped crossing spatial residual decomposition, the expected positive masked residual tends to zero when the absolute full-cell residual and one-sided crossing-cell positive error have vanishing expectations. The masked total residual alone needs integrability. This is critical for original b0 because the root restricts to the true ρ>0 event and some outside-event unmasked values need not be integrable.
-- source:
--   Original b0 positive interior: exact root sum ga121, physical full/cross partition ga94, integrability exact ga122, source full and crossing expected L1 ga119 and ga120.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a125_original_gaussian_masked_full_cross_positive_expected_L1_glue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U F C : ℕ → Ω → ℝ) (mask : Ω → Prop)
    [DecidablePred mask]
    (hSplit : ∀ m ω, U m ω = F m ω + C m ω)
    (hUI : ∀ m, Integrable (fun ω => if mask ω then max (U m ω) 0 else 0) P)
    (hFI : ∀ m, Integrable (fun ω => |F m ω|) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hFT : Tendsto (fun m => ∫ ω, |F m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCT : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω,
      (if mask ω then max (U m ω) 0 else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
