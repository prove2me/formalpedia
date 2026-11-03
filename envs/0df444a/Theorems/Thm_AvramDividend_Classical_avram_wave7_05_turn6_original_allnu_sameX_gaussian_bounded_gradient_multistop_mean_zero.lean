-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_gradient_multistop_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_gradient_multistop_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:44:29.19525+00:00
-- url     : https://prove2.me/theorems/311ce4ba-1e3e-4cf5-b8fd-31dce8f11dda
-- title:
--   Same-source arbitrary-jump stopped Gaussian bounded C2 gradient finite mesh has exact zero expectation
-- statement:
--   For the exact original spectrally negative Lévy source with arbitrary negative jumps, the genuinely ruin-stopped discounted reserve derivative is measurable at each original stopping time. If bounded and globally measurable, its gain against the extracted zero-jump Gaussian Lévy source on the exact same sample space, probability measure and filtration is L1, and a finite stopped mesh sum has mean zero. The Gaussian extraction and decomposition are explicit assumptions.
-- source:
--   Use Proved source C2 multi-stop coefficient predictability UUID 186c0d87-955f-47c7-a5c2-35002ba40cd8 and Proved original Gaussian bounded stopped gain L2/mean-zero UUID 8cf2614f-c9fe-47f1-896a-57969706c910. No external Brownian construction or independent sample space.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_multi_stop_C2_gaussian_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_gradient_multistop_mean_zero
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
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    let F : ι → Ω → ℝ := fun i ω => G i ω * V i ω
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
