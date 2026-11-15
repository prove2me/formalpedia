-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a224_original_true_physical_gaussian_positive_exponential_tail_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a224_original_true_physical_gaussian_positive_exponential_tail_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:04:25.408497+00:00
-- url     : https://prove2.me/theorems/86cb082b-759d-45db-a342-2451ead976fb
-- title:
--   True original Gaussian physical-mesh positive exponential rare-cell source expected L1 vanishes
-- statement:
--   For the actual original zerojump Gaussian X and exact finite-horizon physical grid s_i=i n/(m+1), t_i=s_i+n/(m+1), the expected full physical mesh sum of the positive tail exponential of the centred Gaussian increment converges to zero. No hypothetical surrogate process, stopping mask or nonphysical mesh appears.
-- source:
--   Original source a221 general Gaussian width-integrable Chernoff and genuine n/(m+1) mesh

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a221_original_gaussian_uniform_physical_positive_exponential_tail_L1
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a224_original_true_physical_gaussian_positive_exponential_tail_expected_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (θ δ : ℝ)
    (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let t : ℕ → ℕ → ℝ≥0 := fun m i => s m i + Δ m
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        let Z : ℝ := ((X.X (t m i) ω - X.X (s m i) ω) -
          ((t m i - s m i : ℝ≥0) : ℝ) * X.c) / X.σ
        if δ ≤ Z then Real.exp (θ * Z) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
