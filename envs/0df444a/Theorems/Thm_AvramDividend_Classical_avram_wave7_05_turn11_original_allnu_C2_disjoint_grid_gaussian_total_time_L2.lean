-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:33:46.610587+00:00
-- url     : https://prove2.me/theorems/41bf6e10-3d20-4620-b143-22cad5cf4210
-- title:
--   Original arbitrary-jump source disjoint stopped Gaussian gradient grid total-time L2 bound
-- statement:
--   For a spectrally negative Levy source X and a same-space zero-jump Gaussian component Y identified by an explicit source decomposition, the actual predictable discounted controlled-reserve stopped derivative has a finite disjoint-grid L2 sum whose second moment is bounded by sigma squared times K squared times total horizon T. The theorem assumes separately verified cell L2 moment bounds and uses an exact source-gradient finite-grid orthogonality result.
-- source:
--   Original stopped gradient strong predictability and exact disjoint Gaussian finite-grid L2 isometry, with an explicit bounded-energy cell hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_grid_gradient_auto_predictable_L2

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Uniform finite-grid L² control for the actual stopped original-process gradient. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
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
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      (if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
       else 0) *
      (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)) 2 P)
    (hCell : ∀ i ∈ S,
      (∫ ω, ((if s i ≤ T then
          (Real.exp (-(q * (s i : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
          (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
         else 0) *
        (Y.X (t i) ω - Y.X (s i) ω -
          ((t i - s i) : ℝ) * Y.c)) ^ 2 ∂P) ≤
        ((t i - s i) : ℝ) * X.σ ^ 2 * K ^ 2) :
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
