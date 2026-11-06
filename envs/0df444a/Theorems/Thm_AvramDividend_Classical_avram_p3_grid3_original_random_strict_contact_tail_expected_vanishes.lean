-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
-- name    : AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:16:57.781205+00:00
-- url     : https://prove2.me/theorems/e7ee18f9-74ab-4610-8463-0dc8f6ef953c
-- title:
--   Original random-clock strict contact cash has vanishing expected real value
-- statement:
--   For the original SpectrallyNegativeLevy X and cap-admissible dividend strategy D, any measurable positive contact clock τ bounded by T yields a genuine random strict contact-tail cash. Measurability follows from the actual s-finite dividendMeasure kernel; each tail is dominated by the full strict-horizon cash which is L1; pathwise shrinking-tail convergence and Mathlib dominated convergence give expectation tending to zero.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (τ : Ω → ℝ) (hτ : Measurable τ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτT : ∀ ω, τ ω ≤ (T : ℝ))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo (τ ω - δ n) (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
