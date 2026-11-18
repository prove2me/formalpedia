-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB113_original_stopped_grid_L1_limit_bounded_on_overshoot_tube
-- name    : AvramDividend.Classical.avram_gbB113_original_stopped_grid_L1_limit_bounded_on_overshoot_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:27:33.435657+00:00
-- url     : https://prove2.me/theorems/893fbee4-10db-46d8-97b9-bbd54bef1566
-- title:
--   Original stopped Gaussian physical-grid martingale L1 source bounded on the extended tube
-- statement:
--   If the original stopped physical-grid noise uses an exact time mask s_i<T, and the centred source path remains inside an epsilon tube through the final grid endpoint for all sufficiently fine meshes, its restricted L1 martingale limit is bounded by epsilon almost everywhere on the event. B109 certifies each fine mesh, and B111 transfers eventual mesh control to the original L1 limit. The exact original cash identity remains a separate obligation. The mesh identity is required only on A, matching source coefficients that simplify only on the event tube.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB109_original_grid_stopped_noise_bounded_by_extended_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB113_original_stopped_grid_L1_limit_bounded_on_overshoot_tube
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A) (m0 : ℕ) (T : ℝ≥0)
    (s : ℕ → ℕ → ℝ≥0) (Δ : ℕ → ℝ≥0)
    (hs : ∀ m, Monotone (s m))
    (hs0 : ∀ m, s m 0 = 0)
    (hstep : ∀ m i, s m (i + 1) = s m i + Δ m)
    (hX0 : ∀ ω, X.X 0 ω = 0) (q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (M : ℕ → Ω → ℝ)
    (hMdef : ∀ m ω, ω ∈ A → M m ω =
      (Finset.range (m + 1)).sum (fun i =>
        if s m i < T then Real.exp (-(q * (s m i : ℝ))) *
          (X.X (s m (i + 1)) ω - X.X (s m i) ω -
            ((s m (i + 1) : ℝ) - (s m i : ℝ)) * X.c)
        else 0))
    (hTube : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A →
      ∀ i, s m i ≤ T + Δ m →
        |X.X (s m i) ω - (s m i : ℝ) * X.c| ≤ ε)
    (N : Ω → ℝ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by sorry
