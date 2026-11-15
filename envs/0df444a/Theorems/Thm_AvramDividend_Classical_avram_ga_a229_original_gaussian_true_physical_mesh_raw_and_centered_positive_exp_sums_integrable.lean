-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
-- name    : AvramDividend.Classical.avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:56:36.439615+00:00
-- url     : https://prove2.me/theorems/99ef1c91-e1ff-4442-9eed-887299970f02
-- title:
--   Original Gaussian true physical finite mesh raw and centred positive exponential tails integrable
-- statement:
--   For the original zerojump Gaussian Lévy source on its real physical n/(m+1) mesh, the sum of positive raw exponential large-increment tails and the corresponding centred normalized large-increment exponential tails are both integrable for every mesh size. Uses source-specific single-cell original Gaussian exponential-moment results and finite-sum integrability, closing the auxiliary integrability assumptions in a226.
-- source:
--   Original Gaussian a227 and a228 source Gaussian rare-event one-cell integrability, physical mesh integrable_finset_sum

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a228_original_raw_gaussian_positive_exponential_increment_tail_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (θ δ : ℝ) (hθ : 0 ≤ θ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      (R m i ω - (Δ m : ℝ) * X.c) / X.σ
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) P) ∧
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if δ / (2 * X.σ) ≤ Z m i ω
        then Real.exp ((θ * X.σ) * Z m i ω) else 0) P) := by sorry
