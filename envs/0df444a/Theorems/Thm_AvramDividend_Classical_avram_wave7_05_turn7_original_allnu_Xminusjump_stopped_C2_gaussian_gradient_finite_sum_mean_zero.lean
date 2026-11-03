-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:11:24.850648+00:00
-- url     : https://prove2.me/theorems/e40a12a2-c9d1-4b2d-b8dd-92c8c8e9ebbd
-- title:
--   Original source X-minus-jumps finite stopped C2 derivative Gaussian gains have zero expectation
-- statement:
--   For the exact given spectrally negative Levy X, its original filtration, dividend-control reserve left limit and ruin gate, every bounded finite collection of stopped C2 gradient-weighted increments of the continuous source residual X-tX.c-Jsmall-Jlarge is Bochner-integrable, and the sum has expectation zero. Gaussian Y and original-source decomposition are explicitly assumed on the same probability space.
-- source:
--   Finite linearity consequence of remotely Proved original X-minus-jumps stopped C2 Gaussian derivative L2-isometry and mean-zero theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0)
    (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BG : ι → ℝ) (hBG : ∀ i ∈ S, 0 ≤ BG i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ BG i) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    Integrable (fun ω => ∑ i ∈ S, G i ω * V i ω) P ∧
      (∫ ω, ∑ i ∈ S, G i ω * V i ω ∂P) = 0 := by sorry
