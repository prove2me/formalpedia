-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_factorial_integrable
-- name    : AvramDividend.Classical.avram_mix_fin_source13_original_annulus_factorial_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:20:16.592523+00:00
-- url     : https://prove2.me/theorems/9e92bd41-3cb9-498a-8743-cb90a066e497
-- title:
--   Original annulus factorial count integrable via physical L2
-- statement:
--   On the original Levy process, the negative annulus jump count factorial integrand is integrable at every finite horizon. This follows from the Proved original centred L2 count estimate and the exact polynomial identity, without any extra Gaussian, mark independence, or finite variation assumptions. It is the integrability half of original factorial-moment target 6ea0212e.
-- source:
--   MIX-FIN-SOURCE13 first exact half of original factorial moment target

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin_source13_original_annulus_factorial_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    Integrable (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P := by sorry
