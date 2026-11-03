-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_gaussian_multistop_gradient_automatic_L2_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_gaussian_multistop_gradient_automatic_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:05:52.129534+00:00
-- url     : https://prove2.me/theorems/1efcff85-6921-44f4-bda6-846b3e7a045c
-- title:
--   Original arbitrary-jump same-filtration Gaussian stopped C2 gradients automatically predictable and L2 centred across finite stochastic mesh
-- statement:
--   On the original arbitrary-jump X and its controlled reserve, a same-filtration zero-jump Gaussian component Y with explicit source decomposition yields integrable and mean-zero finite sums of bounded genuinely stopped discounted C2 gradients. Both stopping-time and ambient measurability of every source derivative are automatic, with no separate global measurability hypothesis.
-- source:
--   Combines Proved original all-nu stopped derivative and Hessian measurability UUID 41b798ce-dc51-4499-a4c7-50320ffae570 and Proved ν=0 bounded Gaussian stopped gain UUID 8cf2614f-c9fe-47f1-896a-57969706c910. The existence of same-source Y and jump decomposition remains an explicit bridge.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_gaussian_multistop_gradient_automatic_L2_mean_zero
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
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    let F : ι → Ω → ℝ := fun i ω => G i ω * V i ω
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
