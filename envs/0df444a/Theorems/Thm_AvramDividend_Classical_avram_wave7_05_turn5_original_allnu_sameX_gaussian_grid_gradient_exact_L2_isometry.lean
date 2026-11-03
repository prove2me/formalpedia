-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_grid_gradient_exact_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_grid_gradient_exact_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:37:58.480341+00:00
-- url     : https://prove2.me/theorems/c041bdc7-6759-4826-8182-0aef832b1742
-- title:
--   Same-source arbitrary-jump controlled Gaussian residual finite-grid exact L2 isometry
-- statement:
--   On the canonical arbitrary-jump spectrally negative Levy process and actual ruin-discounted controlled gradient, a finite separated deterministic source grid has exact Gaussian residual weighted L2 isometry and square integrability. The Gaussian Y is on the identical probability space and filtration and is explicitly pathwise linked to X by a required Levy-Ito decomposition.
-- source:
--   Source-specific instantiation of the Proved ν=0 generic finite predictable grid Gaussian L2 isometry with Y, while coefficient G is from actual arbitrary-ν X and same-source pathwise decomposition is an explicit binder. L2 predictability and individual MemLp are assumed and exposed for localisation, not proved here.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_grid_gradient_exact_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
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
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun u ω =>
      if u ≤ T then
        (Real.exp (-(q * (u : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
        (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun _ => (s i : WithTop ℝ≥0)))
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hLp : ∀ i ∈ S,
      MemLp (fun ω => G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)) 2 P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by sorry
