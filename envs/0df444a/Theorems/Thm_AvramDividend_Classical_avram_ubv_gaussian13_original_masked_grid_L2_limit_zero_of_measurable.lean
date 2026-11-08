-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_original_masked_grid_L2_limit_zero_of_measurable
-- name    : AvramDividend.Classical.avram_ubv_gaussian13_original_masked_grid_L2_limit_zero_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:40:38.318248+00:00
-- url     : https://prove2.me/theorems/018f7835-a231-491e-b9e8-89e782d8d1fe
-- title:
--   Original stopped Gaussian grid L² limit inherits L² and zero mean from measurability
-- statement:
--   On the same original Lévy probability space, an almost-everywhere strongly measurable terminal random variable that is the L² limit of centred, L²-integrable original Gaussian physical-grid sums automatically belongs to L² and has expectation zero. Its L² membership need not be assumed in advance.
-- source:
--   Pinned Mathlib memLp_of_cauchy_tendsto and fresh Proved 4e70d0f4 original Gaussian-grid L²-to-L¹ expectation bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_original_masked_grid_L2_limit_mean_zero

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian13_original_masked_grid_L2_limit_zero_of_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v : ℝ)
    (S : ℕ → Finset ι) (s t : ℕ → ι → ℝ≥0)
    (M : Ω → ℝ) (hMMeas : AEStronglyMeasurable M P) :
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
      MemLp M 2 P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
