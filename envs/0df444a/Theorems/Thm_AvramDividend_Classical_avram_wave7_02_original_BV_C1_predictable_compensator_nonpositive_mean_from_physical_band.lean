-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_compensator_nonpositive_mean_from_physical_band
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_predictable_compensator_nonpositive_mean_from_physical_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:57:07.718261+00:00
-- url     : https://prove2.me/theorems/b3f060ab-fe60-4237-b6d0-d81edbae7027
-- title:
--   Original BV stopped negative-jump compensator has nonpositive expected drift from actual C1 physical cap-band integrability
-- statement:
--   For the actual original probability space, Lévy process X, predictable clock, reserve and dividend strategy D, compact positive-cap derivative and first-moment bounds ensure genuine predictable stopped negative-jump kernel measurability and integrability on every finite predictable clock. The exact already-Proved compensator theorem consequently makes the original stopped negative-mark integral have nonpositive real expectation, with no arbitrary measurable-kernel or product-L1 hypothesis. The physically needed cap band and finite mark tail remain explicit; no stopped pathwise Ito identity is claimed.
-- source:
--   Composes already-Proved original d450 predictable kernel measurability and 1a894 source compensator nonpositive expectation with new 935a full C1 cap-band product L1. The only further physical hypothesis is compact positive reserve localization and finite predictable Lévy tail. W8-04 requires this signed drift input.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_source_C1_negative_kernel_product_L1_from_physical_band
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_predictable_compensator_nonpositive_mean_from_physical_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C → 1 ≤ deriv w v)
    (q x : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hOpen : IsOpen {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hBandSmooth : Icc (a / 2) b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (K : ℝ≥0) (hK : ∀ v ∈ Icc (a / 2) b, ‖deriv w v‖₊ ≤ K)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEband : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0) :
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by sorry
