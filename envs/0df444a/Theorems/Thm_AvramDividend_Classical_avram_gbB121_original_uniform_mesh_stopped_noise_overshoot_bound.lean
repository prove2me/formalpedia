-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
-- name    : AvramDividend.Classical.avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:35:18.934021+00:00
-- url     : https://prove2.me/theorems/6ef260dd-c189-402e-aeab-6b3a6fdf4b4d
-- title:
--   Original uniform stopped Gaussian mesh noise is bounded by its extended source tube
-- statement:
--   Specialise the Proved B109 stopped Gaussian noise estimate to the precise source mesh s_i=i*n/(m+1) and step Delta=n/(m+1) used by the original Avram finite-cap theorem. B118 supplies monotonicity, zero start and exact step equality, leaving only the source tube through T+Delta, the start-zero condition and nonnegative discount. This controls the original physical stopped prefix, including the first cell crossing T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB118_original_uniform_physical_grid_monotone_step
import Theorems.Thm_AvramDividend_Classical_avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (n m : ℕ) (T : ℝ≥0)
    (hX0 : X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    (∀ i, s i ≤ T + Δ →
      |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε) →
    |(Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (X.X (s (i + 1)) ω - X.X (s i) ω -
          ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
      else 0)| ≤ ε := by sorry
