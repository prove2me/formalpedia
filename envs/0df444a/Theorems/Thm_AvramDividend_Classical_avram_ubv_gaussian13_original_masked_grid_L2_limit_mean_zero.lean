-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_original_masked_grid_L2_limit_mean_zero
-- name    : AvramDividend.Classical.avram_ubv_gaussian13_original_masked_grid_L2_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:26:40.973197+00:00
-- url     : https://prove2.me/theorems/4e70d0f4-5c05-4a25-b6d6-bbf1212ff19c
-- title:
--   Original masked Gaussian physical-grid L² limit has exactly zero expectation
-- statement:
--   For the original no-jump Lévy process X on its own filtration, consider actual physical deterministic-grid sums of the compact-masked predividend Gaussian gradient times centred original increments. If each grid sum is L² and mean zero, and the grid sums converge in L² to a stopped terminal random variable, that terminal variable has expectation exactly zero. L² convergence directly supplies L¹ convergence on the original probability space, requiring no a.s. limit, pathwise integrable dominating random variable, or filtration change.
-- source:
--   Pinned Mathlib eLpNorm_le_eLpNorm_of_exponent_le and tendsto_integral_of_L1'; complements Proved original predictable finite-grid mean-zero and L² isometries without repeating their contents.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian13_original_masked_grid_L2_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v : ℝ)
    (S : ℕ → Finset ι) (s t : ℕ → ι → ℝ≥0)
    (M : Ω → ℝ) (hM2 : MemLp M 2 P) :
    let G : ℝ≥0 → Ω → ℝ := fun r ω =>
      let y := Function.leftLim
        (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
      X.σ * if y ∈ Icc u v then deriv w y else 0
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G (s n i) ω *
        (X.X (t n i) ω - X.X (s n i) ω -
          ((t n i - s n i) : ℝ) * X.c)
    (∀ n, MemLp (Q n) 2 P) →
    (∀ n, (∫ ω, Q n ω ∂P) = 0) →
    Tendsto (fun n => eLpNorm (Q n - M) 2 P) atTop (𝓝 0) →
      (∫ ω, M ω ∂P) = 0 := by sorry
