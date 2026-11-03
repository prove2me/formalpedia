-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
-- name    : AvramDividend.Classical.avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:46:18.827078+00:00
-- url     : https://prove2.me/theorems/1c9be43b-ad0c-4548-ac2f-3d75e8903498
-- title:
--   Original ruin-inclusive stopped compact positive HJB interior has L1 nonpositive expected negative source jump compensator
-- statement:
--   For the exact original bounded-variation Lévy source and actual dividend-controlled reserve, the compact positive C1 HJB band intersected with t≤the original ruinTime is genuinely predictable, and its discounted negative-mark source compensator is integrable under the physical finite-horizon Lebesgue clock and has nonpositive real expectation. It uses the actual inclusive ruin jump instant, original Ω/P/𝓕/X/D and negative Levy marks, with explicit compact band, first moment, derivative and Lipschitz conditions. This removes free measurable localisation-set hypotheses in the accepted W7-17 compact expected compensator theorem. The intrinsic realised jump compensation equality, zero and cap occupation, Stieltjes atom and stopped terminal remain independent.
-- source:
--   Compose W7-17 accepted exact inclusive source ruin interior predictability 4e14265e, original left reserve strong predictability 94ee9994, and accepted original compact expected negative jump compensator 692ca1e7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_compact_actual_negative_jump_expected_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_inclusive_ruin_predictable_strict_hjb_interior
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
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
    (hMass : X.ν (Iic (-a / 2)) < ⊤) :
    let E : Set (ℝ≥0 × Ω) := {p |
      ((p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C) ∧
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
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
