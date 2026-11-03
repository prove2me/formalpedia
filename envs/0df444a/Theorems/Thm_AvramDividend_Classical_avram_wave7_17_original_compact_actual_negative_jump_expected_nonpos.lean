-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_compact_actual_negative_jump_expected_nonpos
-- name    : AvramDividend.Classical.avram_wave7_17_original_compact_actual_negative_jump_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:39:16.678227+00:00
-- url     : https://prove2.me/theorems/692ca1e7-a4f4-4f12-b03b-dfe358860f96
-- title:
--   Actual compact stopped original negative Levy jump compensator has L1 and nonpositive real expectation
-- statement:
--   On the original spectrally negative Lévy source with bounded variation and physical finite-horizon real Lebesgue clock pushed to nonnegative time, the genuine discounted nonlinear jump kernel on an arbitrary original predictable compact positive-reserve stopped region is integrable in original P expectation and has nonpositive expectation. The actual source kernel is built directly from the controlled original reserve left limit and negative Levy measure; no synthetic G, substitute stochastic source, assumed kernel measurability, or stochastic jump equality. All exact C1 compact localisation, finite negative tail mass, gradient and first moment conditions are retained from the Proved W7-02 compensator.
-- source:
--   Combine source W7-02 Proved 8e5ebef5 expected nonpositive negative compensator with W7-17 d450 source predictable discounted kernel measurability; no other assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_predictable_negative_jump_compensator_expected_nonpos_from_source_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_compact_actual_negative_jump_expected_nonpos
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
    (hD : IsDividendStrategy 𝓕 D)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hCapBand : Icc a b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEstrip : ∀ p ∈ E,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤) :
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by sorry
