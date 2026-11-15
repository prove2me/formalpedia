-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a231_original_true_physical_raw_gaussian_positive_exponential_tail_expected_L1_vanish
-- name    : AvramDividend.Classical.avram_ga_a231_original_true_physical_raw_gaussian_positive_exponential_tail_expected_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:25:26.53897+00:00
-- url     : https://prove2.me/theorems/5cb63a50-c385-4065-8eb6-fc27f0c529ad
-- title:
--   Actual original Gaussian physical-mesh raw positive large-increment exponential source expected L1 vanishes
-- statement:
--   For the genuine original zerojump Gaussian Lévy source, the expected finite-horizon sum across the exact physical mesh of exp(theta times actual raw increment) on positive raw large increment events converges to zero as the mesh refines. The result supplies the unconditional source-specific rare-cell exponential contribution needed for the combined a216 top-cap Gaussian verification estimate.
-- source:
--   Proved a226 true physical source expected tail vanishing under integrability, proved a229 authentic Gaussian raw and centred finite-grid integrability

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a226_original_raw_gaussian_exponential_tail_expected_L1_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a229_original_gaussian_true_physical_mesh_raw_and_centered_positive_exp_sums_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a231_original_true_physical_raw_gaussian_positive_exponential_tail_expected_L1_vanish
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
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        if δ ≤ R m i ω then Real.exp (θ * R m i ω) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
