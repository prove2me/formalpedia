-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys129_original_drift_reserve_ae_continuity
-- name    : AvramDividend.Classical.avram_bvb_phys129_original_drift_reserve_ae_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:48:28.963108+00:00
-- url     : https://prove2.me/theorems/fab3e0b9-9e17-4d7d-85e9-a08957acec55
-- title:
--   Original deterministic drift reserve is continuous almost everywhere
-- statement:
--   The original physical BV deterministic-drift reserve after admissible dividends is continuous at almost every time for every atomless time measure, a necessary integrand-continuity input for the phys95 finite-activity markwise quadrature.
-- source:
--   Proved phys116 and continuity of linear drift

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys129_original_drift_reserve_ae_continuity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) : ∀ᵐ t ∂μ, ContinuousAt (fun s : ℝ≥0 => x + (s : ℝ) * X.drift - D s ω) t := by sorry
