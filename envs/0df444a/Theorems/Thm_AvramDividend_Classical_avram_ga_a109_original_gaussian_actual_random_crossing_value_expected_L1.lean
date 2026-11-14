-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a109_original_gaussian_actual_random_crossing_value_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a109_original_gaussian_actual_random_crossing_value_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:35:38.74361+00:00
-- url     : https://prove2.me/theorems/db52df00-55d5-4c06-ae82-0fe7fc5672ff
-- title:
--   Original Gaussian true randomly selected crossing clipped-source value displacement converges in expected L1 on positive compact band
-- statement:
--   For arbitrary original zero-jump Lévy source random crossing clocks inside one physical mesh width, and a postpayment reserve in an eventual positive compact band, the spatial value increment of the genuine stopped source converges in expected absolute L1 under a single integrable random horizon envelope. No deterministic choice of the crossing index or global value smoothness outside the strictly positive band is required.
-- source:
--   Pinned Mathlib dominated convergence plus proved ga102 original source random crossing a.s. continuity and ga28 compact value modulus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a102_original_gaussian_short_true_crossing_source_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_ga_a28_compact_modulus_last_increment
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a109_original_gaussian_actual_random_crossing_value_expected_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 T ∧ t m ω ∈ Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (α β : ℝ) (hα : 0 < α) (y : ℕ → Ω → ℝ)
    (hBase : ∀ᵐ ω ∂P, ∀ᶠ m in atTop,
      α ≤ y m ω ∧ y m ω ≤ β)
    (w : ℝ → ℝ)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ,
        u ∈ Icc (α / 2) (β + α / 2) →
        v ∈ Icc (α / 2) (β + α / 2) →
        |v - u| < δ → |w v - w u| < ε)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)|) P)
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)| ≤ B ω) :
    Tendsto (fun m => ∫ ω,
      |w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω)) -
        w (y m ω)| ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
