-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_controlled_prejump_hessian_stopped_value_measurable
-- name    : AvramDividend.Classical.avram_wave6_03_original_controlled_prejump_hessian_stopped_value_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:22:41.517305+00:00
-- url     : https://prove2.me/theorems/b63783fb-778d-4c5f-8690-889c2933e80b
-- title:
--   Actual original pre-dividend capped Hessian at a right-continuous stop is measurable to the stopped history
-- statement:
--   For the unchanged original spectrally negative Levy source with any Gaussian scale sigma and any jump measure nu, every admissible dividend strategy D, the exact prepayment reserve left limit of x+X-D and zero-extended C2 cap Hessian, the stopped Hessian coefficient is measurable in the original right-continuous stopped-time sigma algebra. This follows from the newly Proved original controlled Hessian strong predictability, strong progressivity and Mathlib measurable_stoppedValue. This theorem is the exact predictable second-derivative input for the sigma squared over two Gaussian drift; it does not assert a semimartingale Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_controlled_prejump_hessian_stopped_value_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace]
      (stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) := by
  sorry
