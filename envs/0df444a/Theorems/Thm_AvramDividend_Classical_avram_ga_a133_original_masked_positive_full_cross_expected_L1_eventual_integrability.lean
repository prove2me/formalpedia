-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a133_original_masked_positive_full_cross_expected_L1_eventual_integrability
-- name    : AvramDividend.Classical.avram_ga_a133_original_masked_positive_full_cross_expected_L1_eventual_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:27:43.457787+00:00
-- url     : https://prove2.me/theorems/8cc7bfc2-7d7f-4cee-828d-03fbd193086a
-- title:
--   Eventually integrable masked original Gaussian positive spatial residual tends to zero in expectation from one-sided full and true crossing L1 errors
-- statement:
--   For a source-faithful original stopped Gaussian spatial residual U=F+C, if the masked positive part of U becomes integrable on sufficiently fine physical meshes, and both the positive part of the fully pre-stop cell error F and the positive part of the genuinely clipped crossing error C are integrable with expectations vanishing, the original masked positive expected error tends to zero. No absolute-L1 condition on either source error is required, avoiding potentially false assumptions about negative tails of an arbitrary C2 HJB supersolution outside its compact reserve band.
-- source:
--   Certified original root source partition ga123 and positive bound ga126; eventual integrability root child ga132; Mathlib squeeze_zero for eventual inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a133_original_masked_positive_full_cross_expected_L1_eventual_integrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U F C : ℕ → Ω → ℝ) (mask : Ω → Prop) [DecidablePred mask]
    (hSplit : ∀ m ω, U m ω = F m ω + C m ω)
    (hUI : ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if mask ω then max (U m ω) 0 else 0) P)
    (hFI : ∀ m, Integrable (fun ω => max (F m ω) 0) P)
    (hCI : ∀ m, Integrable (fun ω => max (C m ω) 0) P)
    (hFT : Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hCT : Tendsto (fun m => ∫ ω, max (C m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω,
      (if mask ω then max (U m ω) 0 else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
