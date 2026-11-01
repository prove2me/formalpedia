-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
-- name    : AvramDividend.Classical.avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:13:04.776444+00:00
-- url     : https://prove2.me/theorems/af8a1cbf-30a3-4fae-be97-d7a77cae7d20
-- title:
--   Actual stopped original Lévy pre-jump nonlinear marked kernel is predictable–Borel
-- statement:
--   For any genuine original spectrally negative Lévy source, adapted left-continuous dividend strategy and stopping time in its right-continuous filtration, the exact nonlinear source jump kernel times the inclusive survival indicator 1_{s≤τ} is measurable for the right-continuous predictable sigma algebra and Borel jump marks. The equality at the stopping time is essential to retain a ruin-causing source jump, while a right dividend atom at ruin is excluded separately from the reward. This does not assert Poisson jump counts, compensation, martingale expectation, or the BV chain rule.
-- source:
--   Original Avram–Palmowski–Pistorius (2007), Proposition 4(i), stopped nonlinear source martingale interface. Imports two canonically Proved theorems: same-path controlled pre-jump marked kernel measurability 7898252f-6d90-4103-b20b-298e5d9a285a and inclusive stopping-time survival strong predictability 69806d16-1c2a-445a-920f-4500f3645d6a. No surrogate source process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_prejump_marked_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_original_controlled_stopped_prejump_marked_kernel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ) :
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        (if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then (1 : ℝ) else 0) *
        (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
          + p.2) -
         w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))) := by sorry
