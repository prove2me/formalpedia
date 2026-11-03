-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
-- name    : AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:52:32.981663+00:00
-- url     : https://prove2.me/theorems/a5b511f4-876f-4da2-aade-198c6fb1747f
-- title:
--   Exact original-source arbitrary-jump finite C2 mesh split into continuous Gaussian residual and jump remainder
-- statement:
--   For the original X with arbitrary ν and true dividend reserve, assuming explicitly a same-X pathwise Lévy–Itô decomposition X_t=t*c+M_t+Jsmall_t+Jlarge_t, all finite genuine stopping-time mesh C2 centred cells separate exactly into M-based Gaussian cells with σ²/2 and explicit jump derivative, mixed Hessian and squared-jump remainder sums.
-- source:
--   The source-exact one-cell split AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split, conditional samepath decomposition hSourceDecomp; no substituted sample space or unsupported same-X martingale assertion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_cell_split

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (M Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c + M t ω + Jsmall t ω + Jlarge t ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (h : ι → ℝ≥0) :
    let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let A : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    let B : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    let J : ι → Ω → ℝ := fun i ω =>
      (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
      (Jlarge (τ i ω + h i) ω - Jlarge (τ i ω) ω)
    ∀ ω,
      Finset.sum S (fun i => G i ω * A i ω +
        (1 / 2 : ℝ) * H i ω * (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) =
      Finset.sum S (fun i => G i ω * B i ω +
        (1 / 2 : ℝ) * H i ω * (B i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) +
      Finset.sum S (fun i => G i ω * J i ω + H i ω * B i ω * J i ω +
        (1 / 2 : ℝ) * H i ω * J i ω ^ 2) := by sorry
