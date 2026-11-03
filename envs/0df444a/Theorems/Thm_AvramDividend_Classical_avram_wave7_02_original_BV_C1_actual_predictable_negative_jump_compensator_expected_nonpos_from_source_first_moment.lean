-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_predictable_negative_jump_compensator_expected_nonpos_from_source_first_moment
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_predictable_negative_jump_compensator_expected_nonpos_from_source_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:05:50.978476+00:00
-- url     : https://prove2.me/theorems/8e5ebef5-d122-4793-a25e-921da6270ce4
-- title:
--   Actual original BV C1 nonlinear negative Levy compensator expected sign with marked L1 derived from physical first moment
-- statement:
--   For original BV spectrally negative Lévy X and actual dividend-controlled source reserve under compact positive C1 localisation, prove that the physical negative jump compensator of the original predictable source kernel has an L1 sample-wise time-integral and nonpositive expectation. The previously explicit ∀ finite predictable clock marked-product integrability hypothesis is DERIVED from bounded-variation first negative jump moment, true large-tail finite intensity, compact C1 Lipschitz/value bounds, and measurable genuine original controlled source kernel, using proved original marked product L1. Includes negative ruin-overshoots and no artificial source, C2 smoothness or assumed compensation equality.
-- source:
--   Compose new W7-02 full original marked predictable L1 kernel theorem with Proved W7-02 original signed nonlinear expected negative Lévy compensator theorem 1a894711. Exact stochastic realised-jump compensation and stopped C1 chain remain separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_predictable_negative_jump_compensator_expected_nonpos_from_source_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (hq : 0 ≤ q) (D : ℝ≥0 → Ω → ℝ)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hCapBand : Icc a b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (E : Set (ℝ≥0 × Ω))
    (hEstrip : ∀ p ∈ E,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0)
    (hGMeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))] G) :
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by sorry
