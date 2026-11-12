-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb19_original_mixed_source_stopped_C2_mesh_split
-- name    : AvramDividend.Classical.avram_jb19_original_mixed_source_stopped_C2_mesh_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:38:32.784198+00:00
-- url     : https://prove2.me/theorems/64e4089d-7b6d-4cb7-a762-38019b38be53
-- title:
--   Actual original Gaussian and jump source finite-mesh stopped C2 Taylor algebra without a postulated zero-jump process
-- statement:
--   Under only the original intrinsic Gaussian residual limit and original compensated small jump limit for the actual spectrally negative Levy process, construct its all-path Gaussian noise field and obtain the exact stopped finite-mesh C2 identity. Split each original increment into Gaussian residual, compensated small-jump and uncompensated large-jump contributions, with the Gaussian quadratic bracket, mixed cross term and jump square, for exact discounting and ruin-clipped predictable gradient and Hessian coefficients. No separately constructed zero-jump process Y and no cross-space coupling are assumed. The result is finite-mesh algebra, not the continuous-time Ito or dividend Stieltjes cash limit.
-- source:
--   Proved 561f5a08 total original source path and Proved a5b511f4 exact same-path stopped C2 finite mesh. Algebraic input toward 544e8511 and fa7052b1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb19_original_mixed_source_stopped_C2_mesh_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (h : ι → ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) ∧
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
             if 0 < y ∧ ENNReal.ofReal y < C then
               iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
      let A : ι → Ω → ℝ := fun i ω =>
        X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
      let B : ι → Ω → ℝ := fun i ω =>
        M (τ i ω + h i) ω - M (τ i ω) ω
      let J : ι → Ω → ℝ := fun i ω =>
        (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
        (avram_p4_h_gaussian_intrinsic_large_jump_sum X
            (τ i ω + h i) ω -
          avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ i ω) ω)
      ∀ ω,
        Finset.sum S (fun i => G i ω * A i ω +
          (1 / 2 : ℝ) * H i ω *
            (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) =
        Finset.sum S (fun i => G i ω * B i ω +
          (1 / 2 : ℝ) * H i ω *
            (B i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) +
        Finset.sum S (fun i =>
          G i ω * J i ω + H i ω * B i ω * J i ω +
            (1 / 2 : ℝ) * H i ω * J i ω ^ 2) := by sorry
