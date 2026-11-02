-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_stopped_source_L1_L2_jump_tail
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_stopped_source_L1_L2_jump_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:48:56.169202+00:00
-- url     : https://prove2.me/theorems/46258bcf-62db-4de2-84ef-431f86efd5f6
-- title:
--   Actual finite-horizon source predictable time-probability nonlinear jump correction has both vanishing L1 and L2 small-mark tails
-- statement:
--   For every finite horizon on the original source probability P, there is a finite right-continuous predictable observation measure μ that integrates every predictable nonnegative integrand identically to the genuine horizon-trimmed Lebesgue time × P product. For the actual adapted prepayment reserve Taylor correction stopped at ruin, and local C2 interior reserve assumptions plus the nonnegative-half-line boundary behaviour, there is a small negative mark radius on which every decreasing empty-intersection measurable mark tail has simultaneously vanishing absolute L1 jump-generator drift intensity and L2 quadratic jump energy. No compensated martingale or original-source rectangle law is assumed.
-- source:
--   Actual finite-horizon predictable μ and literal product-lintegral identity 16857b34-c56d-4e6d-9b74-2f2983732092, canonically Proved 03-B source L1 drift tail a5fe4f03-2159-444c-bce0-a39e705f2ee0 and source L2 Taylor-energy tail cc000c72-532c-4058-9964-28b4fe4889e6. The same original X, adapted D, ruinTime, 𝓕.rightCont.predictable and X.ν occur throughout; no abstract Poisson substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_stopped_source_L1_L2_jump_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
        Measurable[𝓕.rightCont.predictable] f →
        (∫⁻ p, f p ∂μ) =
          (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P))) ∧
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
      ∃ r : ℝ, 0 < r ∧
        ∀ (B : ℕ → Set ℝ)
          (hBm : ∀ n, MeasurableSet (B n))
          (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
          (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
        (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0 ∧
        (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) = 0 := by sorry
