-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:23:54.638073+00:00
-- url     : https://prove2.me/theorems/1a894711-3991-4021-904d-14a016ce43f7
-- title:
--   Original BV C1 stopped nonlinear negative Levy-mark pathwise compensator is L1 with nonpositive expected value
-- statement:
--   For the genuine original BV controlled Levy source and a C1 candidate with gradient >=1 and zero extension on negative reserves, the original predictable left-surplus negative mark kernel has a nonpositive random finite-physical-horizon ν-compensator expectation, under explicit measurability and product-integrability assumptions. The result handles ruin overshoot marks without C2. This is the compensation SIGN of the original clock, distinct from equality with realised marked jumps and from stopped Ito chain verification.
-- source:
--   Combine accepted original full negative mark value-drop theorem d4e52bb5 with the new W7-02 original predictable mark physical-clock signed Fubini expected-bound theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_predictable_mark_fibre_compensator_expected_nonpositive
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (E : Set (ℝ≥0 × Ω))
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0)
    (hGMeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))] G)
    (hGInt : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))))) :
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by sorry
