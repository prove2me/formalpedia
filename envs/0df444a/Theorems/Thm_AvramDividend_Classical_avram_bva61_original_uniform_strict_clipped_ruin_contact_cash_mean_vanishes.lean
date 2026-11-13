-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
-- name    : AvramDividend.Classical.avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:50:11.991359+00:00
-- url     : https://prove2.me/theorems/c3a02443-d767-4cdd-8017-ef7c1e67ec2e
-- title:
--   Original strict uniform positive-horizon clipped ruin-contact Stieltjes cash mean vanishes
-- statement:
--   For the original controlled spectrally negative Lévy process and arbitrary admissible singular dividend strategy, let the strict uniform-horizon gap be the physical T divided by natural index plus two. The expected discounted Stieltjes cash in the short interval immediately preceding the stopping time clipped by ruin and T tends to zero. The theorem preserves original real-time payment and ruin contact conventions and specialises the already Proved random clipped contact tail L1 theorem to the exact original BV strict grid.
-- source:
--   Exact strict-grid original-process corollary of Proved avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_expected_vanishes
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva61_original_uniform_strict_clipped_ruin_contact_cash_mean_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hTpos : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal - (T : ℝ) / ((n : ℝ) + 2))
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
