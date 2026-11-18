-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB122_original_uniform_stopped_gaussian_L1_source_tube_bound
-- name    : AvramDividend.Classical.avram_gbB122_original_uniform_stopped_gaussian_L1_source_tube_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:44:27.705792+00:00
-- url     : https://prove2.me/theorems/1bd206f7-f74b-45eb-a7aa-125d60369246
-- title:
--   Original uniform stopped Gaussian physical-grid L1 source limit inherits the extended tube bound
-- statement:
--   For the precise uniform grid s_i=i*n/(m+1) of the original finite-cap Gaussian theorem, a stopped Gaussian noise M_m using the original strict s_i<T mask and converging in restricted L1 on A has |N|≤epsilon almost everywhere on A whenever sufficiently fine original meshes stay within the centred source-path epsilon tube through T+Delta_m. This combines the genuine grid B121 with B111 L1 tail transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB121_original_uniform_mesh_stopped_noise_overshoot_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_stopped_gaussian_L1_limit_inherits_eventual_mesh_tube
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB122_original_uniform_stopped_gaussian_L1_source_tube_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A)
    (n m0 : ℕ) (T : ℝ≥0)
    (hX0 : ∀ ω, X.X 0 ω = 0)
    (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (M : ℕ → Ω → ℝ)
    (hMdef : ∀ m ω, ω ∈ A →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      M m ω = (Finset.range (m + 1)).sum (fun i =>
        if s i < T then Real.exp (-(q * (s i : ℝ))) *
          (X.X (s (i + 1)) ω - X.X (s i) ω -
            ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c)
        else 0))
    (hTube : ∀ m, m0 ≤ m → ∀ ω, ω ∈ A →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      ∀ i, s i ≤ T + Δ →
        |X.X (s i) ω - (s i : ℝ) * X.c| ≤ ε)
    (N : Ω → ℝ) (hNI : Integrable N (P.restrict A))
    (hMI : ∀ m, Integrable (M m) (P.restrict A))
    (hL1 : Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ ε := by sorry
