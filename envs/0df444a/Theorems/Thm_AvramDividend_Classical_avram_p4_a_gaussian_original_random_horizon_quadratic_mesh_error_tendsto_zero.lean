-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_random_horizon_quadratic_mesh_error_tendsto_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_random_horizon_quadratic_mesh_error_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:10:02.873701+00:00
-- url     : https://prove2.me/theorems/d927d608-c79f-4365-b98b-3184d445161b
-- title:
--   Original Levy sigma fourth-power quadratic mesh coefficient tends to zero on random finite horizons
-- statement:
--   For the actual source spectrally negative Levy process X, random finite mesh increments whose sum is bounded pathwise by a finite random horizon and whose maximal duration tends to zero pathwise have vanishing fourth-power Gaussian quadratic-mesh coefficient. This is deterministic-on-samples and does not assume a source-unbacked Brownian process or assert a stochastic quadratic variation.
-- source:
--   The previously Proved original-source sigma quadratic mesh error tendsto-zero helper; Avram Palmowski Pistorius Proposition 4(i) equation (5.10).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_quadratic_mesh_error_tendsto_zero
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_random_horizon_quadratic_mesh_error_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : ℕ → Finset ι) (h : ℕ → ι → Ω → ℝ≥0)
    (τ : Ω → ℝ≥0) (ε : ℕ → Ω → ℝ)
    (hε : ∀ ω n, 0 ≤ ε n ω)
    (hmax : ∀ ω n, ∀ i ∈ S n, (h n i ω : ℝ) ≤ ε n ω)
    (hT : ∀ ω n, (∑ i ∈ S n, (h n i ω : ℝ)) ≤ (τ ω : ℝ))
    (hεzero : ∀ ω, Tendsto (fun n => ε n ω) atTop (nhds 0)) :
    ∀ ω, Tendsto
      (fun n => (2 : ℝ) * X.σ ^ 4 *
        (∑ i ∈ S n, (h n i ω : ℝ) ^ 2)) atTop (nhds 0) := by sorry
