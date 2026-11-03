-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_C2_L1_mesh_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_C2_L1_mesh_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:06:58.259379+00:00
-- url     : https://prove2.me/theorems/6e7bb2ce-1280-4582-af1d-980fa4bd0278
-- title:
--   Original arbitrary-jump Gaussian C2 stopped-mesh L1 limit preserves zero expectation
-- statement:
--   For the actual controlled original Lévy process with arbitrary jumps and same-source Gaussian component Y under explicit decomposition, a refining sequence of finite genuinely stopped C2 Gaussian residual sums converging in L1 to an integrable random limit has zero expectation. This isolates the exact localisation/mesh convergence hypothesis required to promote the finite Gaussian identities to the continuous martingale.
-- source:
--   Proved finite source Gaussian centred C2 mesh meanzero UUID 1f73818b-86d9-4198-b9b8-43a9852bdfca plus pinned MeasureTheory.tendsto_integral_of_L1 from Mathlib.MeasureTheory.Integral.Bochner.Basic. Every source coefficient, stopping-time and moment hypothesis is indexed by mesh n. L1 limit and same-source Levy-Ito extraction remain explicit unproved obligations.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_C2_L1_mesh_limit_mean_zero
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
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n, ∀ i ∈ S n, G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (hHsource : ∀ n, ∀ i ∈ S n, H n i = fun ω =>
      (1 / 2 : ℝ) * (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0))) ω)
    (hGI : ∀ n, ∀ i ∈ S n, Integrable (fun ω => G n i ω *
      (Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
        (h n i : ℝ) * Y.c)) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n, Integrable (fun ω => H n i ω *
      (Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
        (h n i : ℝ) * Y.c) ^ 2) P)
    (M : Ω → ℝ) (hMI : Integrable M P) :
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
        (h n i : ℝ) * Y.c
    let F : ℕ → Ω → ℝ := fun n ω => Finset.sum (S n) (fun i =>
      G n i ω * V n i ω +
        (H n i ω * V n i ω ^ 2 -
          ((h n i : ℝ) * X.σ ^ 2) * H n i ω))
    Tendsto (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P) atTop (nhds 0) →
      (∫ ω, M ω ∂P) = 0 := by sorry
