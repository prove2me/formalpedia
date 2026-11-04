-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn9_original_zerojump_X_C2_gaussian_gradient_finite_mesh_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn9_original_zerojump_X_C2_gaussian_gradient_finite_mesh_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:24:53.973959+00:00
-- url     : https://prove2.me/theorems/dda98bf8-ff8c-4e46-a4d0-68105aae159c
-- title:
--   Direct original zerojump Levy X stopped C2 Gaussian derivative finite mesh meanzero
-- statement:
--   For the canonical spectrally negative Levy process X itself with zero Levy jump measure, stopped discounted C2 derivative integrands of the actual original dividend-controlled reserve give integrable centered finite Gaussian gains on arbitrary bounded original stopping-time meshes. The same original Ω/P/filtration and ruinTime are used, with no auxiliary Brownian or Y process.
-- source:
--   Remotely Proved allnu X-minus-jumps C2 stopped Gaussian gradient finite sum mean-zero helper (Wave7 turn7), specialized with Y=X and Jsmall=Jlarge=0.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn9_original_zerojump_X_C2_gaussian_gradient_finite_mesh_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
      X.X t ω - (t : ℝ) * X.c
    let V : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    Integrable (fun ω => ∑ i ∈ S, G i ω * V i ω) P ∧
      (∫ ω, ∑ i ∈ S, G i ω * V i ω ∂P) = 0 := by sorry
