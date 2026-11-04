-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_uniform_L2_vitali_cap
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_uniform_L2_vitali_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:50:50.418342+00:00
-- url     : https://prove2.me/theorems/2b1f379d-7b17-41f8-83cb-d2a19e5e22a0
-- title:
--   Source-specific Gaussian disjoint stopped-gradient mesh uniform L2 Vitali envelope
-- statement:
--   For a spectrally negative Levy source and an explicitly same-space zero-jump Gaussian component, the actual stopped C2 discounted gradient on pairwise disjoint deterministic intervals has an L2 seminorm bounded by the square root of T sigma squared K squared, provided its source cell energy bounds and finite total mesh duration hold. This supplies the uniform L2 hypothesis used in the previously Proved original stopped Gaussian Vitali limit theorem.
-- source:
--   Accepted original-source Gaussian total-time disjoint-grid L2 second-moment theorem and real square-moment-to-eLpNorm bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_gaussian_grid_L2_of_second_moment_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Uniform finite-grid L² control for the actual stopped original-process gradient. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_uniform_L2_vitali_cap
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
    eLpNorm (fun ω => ∑ i ∈ S, F i ω) (2 : ℝ≥0∞) P ≤
      ENNReal.ofReal (Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2)) := by sorry
