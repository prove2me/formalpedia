-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_full_L1_stopped_ito_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_full_L1_stopped_ito_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:31:26.735957+00:00
-- url     : https://prove2.me/theorems/94037a94-1916-40fe-81ca-ff389a3c8857
-- title:
--   Direct original zero-jump stopped C2 Gaussian Ito L1-limit martingale expectation zero
-- statement:
--   For the given original spectrally negative Levy X with X.nu=0, its exact original filtration, dividend reserve left limit, C2 derivative and Hessian ruin-gated mesh sums, if the centred Gaussian Ito residuals converge in L1 to integrable Z, then E Z=0. All Gaussian increments are actual X.X increments; there is no auxiliary witness, independent space or jump decomposition assumption.
-- source:
--   Specialisation of remotely Proved original-source all-nu stopped C2 Gaussian full L1 mesh residual expectation-zero result with Y=X and zero jump fields.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_source_C2_gaussian_full_L1_stopped_ito_limit_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_full_L1_stopped_ito_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
    (hHsource : ∀ n, ∀ i ∈ S n, H n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (BG BH : ℕ → ι → ℝ)
    (hBG : ∀ n, ∀ i ∈ S n, 0 ≤ BG n i)
    (hBH : ∀ n, ∀ i ∈ S n, 0 ≤ BH n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ BG n i)
    (hHbound : ∀ n, ∀ i ∈ S n, ∀ ω, |H n i ω| ≤ BH n i)
    (Z : Ω → ℝ) (hZI : Integrable Z P) :
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      X.X (τ n i ω + h n i) ω - X.X (τ n i ω) ω -
        (h n i : ℝ) * X.c
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, (G n i ω * V n i ω + (1 / 2 : ℝ) * H n i ω *
        (V n i ω ^ 2 - (h n i : ℝ) * X.σ ^ 2))
    Tendsto (fun n => ∫⁻ ω, ‖Q n ω - Z ω‖ₑ ∂P) atTop (nhds 0) →
      (∫ ω, Z ω ∂P) = 0 := by sorry
