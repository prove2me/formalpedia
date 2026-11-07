-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_ruin_contact_tail_expected_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_original_uniform_ruin_contact_tail_expected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:37:07.863885+00:00
-- url     : https://prove2.me/theorems/21094092-0791-42d6-864a-40f9748a1d8e
-- title:
--   Expected original stopped ruin-contact discounted dividend tail vanishes on the exact physical uniform mesh
-- statement:
--   Specialise the proven original ruin-clipped contact tail expected-vanishing theorem to the exact physical uniform grid width T/(n+2), using the proven positive, antitone, tending-to-zero margin. The tail is over the actual paymentTimes, original D and ruinTime X x D. This isolates the precise L1 contact error needed by the signed Fatou physical grid witness 2bc848f9 and 965af42c, without assuming no ruin atoms or simplifying the stopped process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_clipped_ruin_contact_tail_expected_vanishes
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_uniform_ruin_contact_tail_expected_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal -
                (T : ℝ) / ((n : ℝ) + 2))
              ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
