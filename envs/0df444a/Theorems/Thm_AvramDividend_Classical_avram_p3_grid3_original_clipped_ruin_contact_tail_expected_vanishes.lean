-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
-- name    : AvramDividend.Classical.avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:59:00.637147+00:00
-- url     : https://prove2.me/theorems/615a6aca-3235-49d6-a22f-71ab71514f9a
-- title:
--   Actual original ruin-clipped strict contact-tail cash has vanishing expected value
-- statement:
--   Specialise original moving-clock strict contact-tail expected convergence to the genuine clipped original ruin time min(ruinTime X x D ω,T), using the independently proved real measurability, nonnegativity and horizon upper bound of that clock. This provides exactly the stopped physical contact cash L1 limit needed by the signed Fatou grid construction.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal - δ n)
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
