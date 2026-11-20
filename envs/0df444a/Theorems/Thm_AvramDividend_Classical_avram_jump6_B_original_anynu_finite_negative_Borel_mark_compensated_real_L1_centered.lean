-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
-- name    : AvramDividend.Classical.avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:00:44.772533+00:00
-- url     : https://prove2.me/theorems/181c4d7f-073f-43e9-934d-18ee36f82cc7
-- title:
--   Actual original any-activity finite negative-mark Borel cell centred real L1 and zero mean from automatic compensator rate
-- statement:
--   On the original spectrally negative Levy process with arbitrary negative-jump intensity, any Borel set B contained in negative marks and satisfying finite local Levy measure X.ν(B)<infinity has a real compensated count in any deterministic interval (s,t] that is integrable and has expectation zero. The true compensator intensity rate is obtained from the proved arbitrary negative-Borel predictable simple mark formula with constant unit weight and its original probability law. Neither finite full negative-jump intensity nor a supplied rate hypothesis is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_predictable_negative_Borel_simple_marked_compensation_no_rate_hypothesis_20261117
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_centered_jump_mean_zero
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
      (∫ ω, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 := by sorry
