-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys117_original_admissible_dividend_ae_rightLim_eq
-- name    : AvramDividend.Classical.avram_bvb_phys117_original_admissible_dividend_ae_rightLim_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:57:12.894376+00:00
-- url     : https://prove2.me/theorems/f70380ff-1bfd-49ef-85b8-aab554c5f036
-- title:
--   Original admissible dividend strict right limit equals the path almost everywhere
-- statement:
--   For any original admissible dividend strategy and any atomless measure of nonnegative time, the strict right limit of the cumulative dividend path agrees with its value almost everywhere. The proof combines Proved phys116, which annihilates the discontinuity set, with Mathlib's right-limit equality at continuous points. It supplies physical-grid reserve continuity for the original phys95.
-- source:
--   Original BV phys95 reserve path; Proved phys116 and Mathlib ContinuousWithinAt.rightLim_eq

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys117_original_admissible_dividend_ae_rightLim_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) : ∀ᵐ t ∂μ, Function.rightLim (fun s : ℝ≥0 => D s ω) t = D t ω := by sorry
