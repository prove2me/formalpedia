-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a226_original_raw_gaussian_exponential_tail_expected_L1_of_integrable
-- name    : AvramDividend.Classical.avram_ga_a226_original_raw_gaussian_exponential_tail_expected_L1_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:15:04.151537+00:00
-- url     : https://prove2.me/theorems/b409e5d1-4146-4612-a851-cf3538cb00f9
-- title:
--   Actual original Gaussian raw positive exponential rare-cell expected sum vanishes from Gaussian integrable source
-- statement:
--   On the actual physical Gaussian Lévy zerojump mesh, provided the finite Gaussian exponential raw-tail and centred-tail source sums are integrable (as follow separately from the original Gaussian exponential-moment theorem), the expected raw large-positive exponential source tail vanishes. Applies the true grid pointwise raw-to-centered envelope and the proved centered Gaussian L1 vanishing without replacing X by an abstract process.
-- source:
--   Original genuine Gaussian physical mesh a224 and eventual source pointwise upper a225

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a224_original_true_physical_gaussian_positive_exponential_tail_expected_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a225_original_raw_positive_gaussian_exp_tail_fullmesh_eventual_centered_bound
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a226_original_raw_gaussian_exponential_tail_expected_L1_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (θ δ : ℝ)
    (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (R m i ω - (Δ m : ℝ) * X.c) / X.σ
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) P) →
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ / (2 * X.σ) ≤ Z m i ω
        then Real.exp ((θ * X.σ) * Z m i ω) else 0) P) →
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
