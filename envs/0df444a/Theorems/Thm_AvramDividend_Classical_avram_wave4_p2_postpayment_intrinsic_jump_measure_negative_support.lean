-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_jump_measure_negative_support
-- name    : AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_jump_measure_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:02:46.396466+00:00
-- url     : https://prove2.me/theorems/d4e640fe-5b2b-4bde-82ec-80fe7aa1395c
-- title:
--   Actual postpayment Lévy and dividend jump measure has no nonnegative marks
-- statement:
--   For the actual original-filtration spectrally negative Lévy surplus controlled by any admissible dividend strategy, the full intrinsic positive-time postpayment jump measure assigns zero mass to each rectangle (s,t] × [0,∞). Every nonzero combined jump mark ΔX−(D_{t+}−D_t) is negative, even at simultaneous Lévy and dividend jumps. This is a pathwise measure-level spectral-support fact, not a claimed Lévy Poisson compensator for the controlled measure.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), (5.11)–(5.12). Canonical postpayment intrinsic measure equality 282556df, joint combined-mark measurability 0c60d413, actual source no-positive-jump e95fe5bc, and dividend path rightLimit monotonicity 953f0e91. Original-source measure-level analogue 12e84fff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_jump_measure_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)))
      (Ioc s t ×ˢ Ici (0 : ℝ)) = 0 := by sorry
