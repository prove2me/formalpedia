-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
-- name    : AvramDividend.Classical.avram_bvb_phys116_original_admissible_dividend_ae_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:07:12.139753+00:00
-- url     : https://prove2.me/theorems/6e3d7e31-7ede-4c58-a280-dac4bc98ab97
-- title:
--   Every original admissible dividend path is a.e. continuous for atomless time measures
-- statement:
--   The cumulative dividend path of an original admissible spectrally negative Levy strategy has zero discontinuity mass for any atomless time measure at every sample path. IsAdmissibleLe implies IsDividendStrategy, hence monotonicity in time; Mathlib shows the discontinuity set is countable. This yields an almost-everywhere time continuity fact for the physical uniform-grid quadrature phys95, including Lebesgue time measures.
-- source:
--   Original DividendStrategy definition and Mathlib Monotone.countable_not_continuousAt

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys116_original_admissible_dividend_ae_continuity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) : μ {t : ℝ≥0 | ¬ ContinuousAt (fun s : ℝ≥0 => D s ω) t} = 0 := by sorry
