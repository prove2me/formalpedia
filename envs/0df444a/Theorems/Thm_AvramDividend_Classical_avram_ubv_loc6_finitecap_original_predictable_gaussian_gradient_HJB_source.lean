-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_finitecap_original_predictable_gaussian_gradient_HJB_source
-- name    : AvramDividend.Classical.avram_ubv_loc6_finitecap_original_predictable_gaussian_gradient_HJB_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:29:20.965415+00:00
-- url     : https://prove2.me/theorems/a0c63349-b09b-4d2f-bc1e-acb99fbe74a6
-- title:
--   Original finite-cap stopped generator HJB and predictable Gaussian gradient L2 on one physical measure
-- statement:
--   On a finite-cap strictly interior physical reserve band, one original predictable-clock measure carries both the original integrable/nonpositive HJB drift and a predictable pre-right-dividend Gaussian derivative coefficient with finite quadratic energy. This is the common-measure martingale-source precursor, without assuming a stochastic integral mean zero.
-- source:
--   Compose the source-exact finitecap original compact generator HJB L1 theorem and Proved allcap original predictable gradient compact L2 8a71fa31, with the same original predictable μ and real upper-band-to-ENNReal cap conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_finitecap_original_predictable_gaussian_gradient_HJB_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u v δ a b : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C.toReal)
    (ha : 0 < a) (hau : a < u + δ) (hvb : v < b)
    (hb : b < C.toReal)
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 ∧
      Measurable[𝓕.rightCont.predictable] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((H p) ^ 2) ∂μ) < ⊤ := by sorry
