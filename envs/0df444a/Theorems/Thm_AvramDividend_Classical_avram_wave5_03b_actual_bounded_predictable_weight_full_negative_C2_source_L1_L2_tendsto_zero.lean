-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_bounded_predictable_weight_full_negative_C2_source_L1_L2_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_bounded_predictable_weight_full_negative_C2_source_L1_L2_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:23:36.745002+00:00
-- url     : https://prove2.me/theorems/39436459-3aa4-4586-bb40-76dcfa97c336
-- title:
--   Actual controlled predictable bounded-weight full negative nonlinear Taylor L1 and L2 small-jump energy vanish
-- statement:
--   For the actual spectrally negative Lévy source X, original adapted dividend control D, interior C² w, prepayment reserve Y=leftLim(x+X.X-rightLimit D), and the inclusive ruin-stopped nonlinear negative-mark Taylor remainder HS, let μ be any finite measure on the actual right-continuous predictable sigma algebra. For every measurable antitone sequence of negative mark cuts with empty intersection, and every predictable real weight ρ with 0≤ρ≤1, both the absolute weighted HS intensity L1 small-mark mass and the squared weighted HS intensity L2 small-mark energy tend to zero ordinarily along atTop under the literal μ and source X.ν. This is source-intensity convergence, not a compensated martingale or abstract Poisson law.
-- source:
--   Canonical Proved decd1b90 original-source general C² stopped nonlinear Taylor full-negative L1 and L2 small-mark energy Tendsto. Prove pointwise bounded predictable weight contraction in real absolute values and squares, then apply nested lintegral monotonicity and order squeeze to both source intensity tails.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_L1_L2_tendsto_zero

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_bounded_predictable_weight_full_negative_C2_source_L1_L2_tendsto_zero
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (ρ : ℝ≥0 × Ω → ℝ)
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
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|ρ p * HS (p,z)|) ∂X.ν ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((ρ p * HS (p,z)) ^ 2) ∂X.ν ∂μ)
      atTop (𝓝 0) := by sorry
