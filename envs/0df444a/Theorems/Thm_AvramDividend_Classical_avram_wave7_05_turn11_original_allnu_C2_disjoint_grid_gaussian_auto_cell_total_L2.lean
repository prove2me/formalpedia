-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_auto_cell_total_L2
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_auto_cell_total_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:59:46.547757+00:00
-- url     : https://prove2.me/theorems/3d4ab486-9e75-403f-bc1e-82e11d4851eb
-- title:
--   Original stopped C2 disjoint Gaussian grid L2 bound with automatic source cell energy
-- statement:
--   On the genuine original spectrally negative Levy space, the source discounted stopped C2 gradient at deterministic grid starts is bounded by K and identified with the stoppedValue original predictable process. Each cell automatically satisfies the L2 and exact-duration second-moment bound by the accepted original Gaussian one-cell theorem; pairwise disjoint Gaussian gains then have total second moment at most T sigma squared K squared. This theorem removes the separate per-cell L2 and energy hypotheses of the preceding grid estimate, retaining only explicit source identity and boundedness.
-- source:
--   Accepted original X-minus-jumps stopped C2 Gaussian gradient cell-time bound, original disjoint Gaussian grid L2 exact-time estimate, and Mathlib deterministic stopping time measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_stopped_C2_gradient_cell_sigma_time_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Uniform finite-grid L² control for the actual stopped original-process gradient. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_auto_cell_total_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (hTotal : (∑ i ∈ S, ((t i - s i) : ℝ≥0) : ℝ) ≤ (T : ℝ))
    (K : ℝ) (hK : 0 ≤ K)
    (hGsource : ∀ i ∈ S,
      (fun ω => if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) = stoppedValue (fun u ω =>
        if u ≤ T then
          (Real.exp (-(q * (u : ℝ))) *
            deriv w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
          (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun _ : Ω => (s i : WithTop ℝ≥0)))
    (hGbound : ∀ i ∈ S, ∀ ω,
      |if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0| ≤ K) :
    let G : ℕ → Ω → ℝ := fun i ω =>
      if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0
    let F : ℕ → Ω → ℝ := fun i ω =>
      G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
      (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) ≤
        (T : ℝ) * X.σ ^ 2 * K ^ 2 := by sorry
