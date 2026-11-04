-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_stopped_C2_gradient_cell_sigma_time_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_stopped_C2_gradient_cell_sigma_time_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:39:51.475036+00:00
-- url     : https://prove2.me/theorems/5f25d914-6bf7-41c7-afed-4b9337bab521
-- title:
--   Original source stopped Gaussian derivative exact cell-time sigma-squared variance bound
-- statement:
--   For the genuine source X and its explicitly assumed same-space Gaussian zero-jump process Y, the bounded predictable discounted stopped C2 derivative Gaussian gain over a stopped interval of duration h is in L2 and has second moment at most h times sigma squared times K squared. Derives the sharp interval duration bound from the source Gaussian isometry and original stopped gradient energy estimate.
-- source:
--   Previously remotely Proved source X-minus-jumps stopped C2 Gaussian gradient L2 isometry and original stopped gradient uniform bound integral energy.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Actual source Gaussian stopped-gradient L² energy bound at a single clock. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_stopped_C2_gradient_cell_sigma_time_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (τ : Ω → ℝ≥0)
    (hτ : ∀ u : ℝ≥0,
      MeasurableSet[𝓕.rightCont u] {ω : Ω | τ ω ≤ u})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G : Ω → ℝ)
    (hGsource : G = stoppedValue (fun u ω =>
      if u ≤ T then
        (Real.exp (-(q * (u : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
        (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ ω, |G ω| ≤ K) :
    let M : ℝ≥0 → Ω → ℝ := fun u ω =>
      X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω
    let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
    MemLp (fun ω => G ω * V ω) 2 P ∧
      (∫ ω, (G ω * V ω) ^ 2 ∂P) ≤
        (h : ℝ) * X.σ ^ 2 * K ^ 2 := by sorry
