-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_bounded_predictable_weight_taylor_negative_mark_L1_tail
-- name    : AvramDividend.Classical.avram_wave6_04_actual_bounded_predictable_weight_taylor_negative_mark_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:04:26.558212+00:00
-- url     : https://prove2.me/theorems/2ee9f60c-4134-4670-9038-cb6629187d07
-- title:
--   Every positive bounded predictable weight preserves full actual source stopped nonlinear Taylor negative-mark L¹ tail decay
-- statement:
--   For the actual spectrally negative Lévy source X, its Lévy measure X.ν on all negative real marks, original dividend strategy D, prepayment left-limit surplus, exact inclusive ruinTime, and a negative-extended interior C² test function w, every physical predictable weight ρ in [0,1] preserves vanishing original source Taylor remainder first-moment intensity on arbitrary antitone measurable negative mark bands B_n decreasing to ∅. The input is a finite authentic right-continuous predictable clock μ; this reuses the already Proved full-negative Taylor L1 band-tail theorem, supplies direct random-discount finite-band convergence for Chat06, and does not assert a generic compensator or require Chat01's outstanding original source count law.
-- source:
--   Avram Wave6 Chat04, source-specific negative Taylor full-mark tail weighted by genuine bounded predictable ρ, direct from Proved 19668eea. Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_bounded_predictable_weight_taylor_negative_mark_L1_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (ρ : (ℝ≥0 × Ω) → ℝ)
    (hρm : Measurable[𝓕.rightCont.predictable] ρ)
    (hρ : ∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    ∀ (B : ℕ → Set ℝ)
      (hBm : ∀ n, MeasurableSet (B n))
      (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
      (hBanti : Antitone B)
      (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|ρ p * HS (p,z)|) ∂X.ν ∂μ) = 0 := by sorry
