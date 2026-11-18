-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_fixed_grid_GH_L1_long_tube_bound
-- name    : AvramDividend.Classical.avram_gaussianB_original_fixed_grid_GH_L1_long_tube_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:49:33.335352+00:00
-- url     : https://prove2.me/theorems/c552a4f6-4b97-43fe-845e-3aa9b0d3aa1f
-- title:
--   Original finite stopped Gaussian G/H mesh L1 bound on every physical grid beyond explicit m0 refinement threshold
-- statement:
--   On the actual physical mesh Δ_m=n/(m+1), once m0+1≥16000n, every right endpoint of the original stopped Gaussian G/H grid through T=1/1000 lies in the same fixed positive-probability Brownian event through 17/16000. The Proved source-specific G/H L1 theorem therefore bounds the original restricted-L1 limit noise |N| by ε on the event, conditional only on the original integrability, coefficients, path, and L1 convergence hypotheses.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB182_long_tube_original_GH_L1_noise_bound_with_grid_overshoot
import Theorems.Thm_AvramDividend_Classical_avram_gbB183_uniform_physical_grid_step_fits_centered_long_tube
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_fixed_grid_GH_L1_long_tube_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A)
    (m0 : ℕ) (T : ℝ≥0) (s : ℕ → ℕ → ℝ≥0)
    (Δ : ℕ → ℝ≥0)
    (hs : ∀ m, Monotone (s m))
    (hs0 : ∀ m, s m 0 = 0)
    (hstep : ∀ m i, s m (i + 1) = s m i + Δ m)
    (hX0 : ∀ ω, X.X 0 ω = 0)
    (q ε a : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (w : ℝ → ℝ)
    (B : Ω → ℝ≥0 → ℝ)
    (hT : T = (1 / 1000 : ℝ≥0))
    (hSource : ∀ ω, ω ∈ A → ∀ s : ℝ≥0,
      s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B ω s + 2 * (s : ℝ))
    (hCentered : ∀ ω, ω ∈ A → ∀ s : ℝ≥0,
      s ≤ (1 / 1000 : ℝ≥0) →
      |B ω s| ≤ (1 / 4000 : ℝ))
    (hLongSource : ∀ ω, ω ∈ A → ∀ u : ℝ≥0,
      u ≤ (17 / 16000 : ℝ≥0) →
      X.X u ω = B ω u + 2 * (u : ℝ))
    (hLongCentered : ∀ ω, ω ∈ A → ∀ u : ℝ≥0,
      u ≤ (17 / 16000 : ℝ≥0) →
      |B ω u| ≤ (1 / 4000 : ℝ))
    (hc : X.c = (2 : ℝ))
    (n : ℕ)
    (hΔdef : ∀ m, Δ m =
      (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))
    (hm0 : 16000 * n ≤ m0 + 1)
    (hεbound : (1 / 4000 : ℝ) ≤ ε)
    (v : ℕ → ℕ → ℝ) (M : ℕ → Ω → ℝ)
    (hMdef : ∀ m ω, ω ∈ A →
      let Y : ℕ → ℝ := fun i =>
        (1 / 8 : ℝ) + X.X (s m i) ω -
          rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ))
            (s m i) ω
      let Z : ℕ → ℝ := fun i =>
        X.X (s m (i + 1)) ω - X.X (s m i) ω -
          ((s m (i + 1) : ℝ) - (s m i : ℝ)) * X.c
      M m ω = (Finset.range (m + 1)).sum (fun i =>
        (if s m i < T then Real.exp (-(q * (s m i : ℝ))) *
          (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
        else 0) * Z i +
        (if s m i < T then (1 / 2 : ℝ) *
          Real.exp (-(q * (s m i : ℝ))) *
          (if Y i ∈ Icc a (5 / 44 : ℝ) then
            iteratedDeriv 2 w (Y i) else 0)
        else 0) * (Z i ^ 2 - v m i)))
    (N : Ω → ℝ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by sorry
