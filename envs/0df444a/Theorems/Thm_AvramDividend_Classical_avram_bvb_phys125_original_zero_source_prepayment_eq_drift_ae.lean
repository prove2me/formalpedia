-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys125_original_zero_source_prepayment_eq_drift_ae
-- name    : AvramDividend.Classical.avram_bvb_phys125_original_zero_source_prepayment_eq_drift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:34:33.763395+00:00
-- url     : https://prove2.me/theorems/f43a40bf-6cce-4537-98ae-f6de1a6422c3
-- title:
--   Original zero-source prepayment reserve equals drift reserve almost everywhere
-- statement:
--   Under original admissibility and at almost every positive time for any atomless time measure, the prepayment left-limit of the physical no-source-jump BV drift reserve equals the ordinary x+drift·t−D(t) reserve. This is an essential one-sided convergence fact for the marked Lévy compensator kernel in phys95, retaining the original dividend and ruin conventions.
-- source:
--   Proved phys116 original dividend a.e. continuity, phys124 drift prepayment left-limit identity and Mathlib nhdsLT_neBot_of_exists_lt

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys116_original_admissible_dividend_ae_continuity
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys124_original_zero_source_drift_prepayment_leftLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys125_original_zero_source_prepayment_eq_drift_ae {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) : ∀ᵐ t ∂μ, 0 < (t : ℝ≥0) → Function.leftLim (fun s : ℝ≥0 => x + (s : ℝ) * X.drift - rightLimit D s ω) t = x + (t : ℝ) * X.drift - D t ω := by sorry
