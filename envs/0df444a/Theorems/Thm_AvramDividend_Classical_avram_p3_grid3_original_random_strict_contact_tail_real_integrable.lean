-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_real_integrable
-- name    : AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:23:14.75233+00:00
-- url     : https://prove2.me/theorems/c778954a-ff3d-4b71-b499-24dd128dd7b3
-- title:
--   Original measurable random strict contact-interval cash is L1
-- statement:
--   Every genuine moving strict contact-interval real discounted dividend cash is integrable under an original cap-admissible strategy, for an arbitrary measurable positive contact clock bounded by the horizon. The actual dividendMeasure kernel gives measurability, while the pathwise interval bound and original strict-horizon L1 theorem supply the integrable dominating random variable.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_masked_contact_tail_real_le_full_strict_cash
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_real_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (τ : Ω → ℝ) (hτ : Measurable τ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hτT : ∀ ω, τ ω ≤ (T : ℝ))
    (δ : ℝ) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo (τ ω - δ) (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
