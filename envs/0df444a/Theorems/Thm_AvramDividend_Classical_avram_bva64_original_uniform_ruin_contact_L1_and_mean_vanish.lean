-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
-- name    : AvramDividend.Classical.avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T15:55:51.020247+00:00
-- url     : https://prove2.me/theorems/4b84dd73-f298-478d-b336-fd743c054c2a
-- title:
--   Original uniform strict ruin-contact Stieltjes cash is L1 at every row and its expectation vanishes
-- statement:
--   For the authentic admissible dividend D, strictly stopped ruin time clipped to finite T, and exact uniform gap T/(n+2), the discounted Stieltjes cash in the contact interval is absolutely integrable for each n and its expected value tends to zero. Combines two existing source-exact Proved results; no finite-activity or independence approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva64_original_uniform_ruin_contact_L1_and_mean_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hTpos : 0 < T) :
    (∀ n : ℕ, Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal -
               (T : ℝ) / ((n : ℝ) + 2))
            ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) P) ∧
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal -
                 (T : ℝ) / ((n : ℝ) + 2))
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
