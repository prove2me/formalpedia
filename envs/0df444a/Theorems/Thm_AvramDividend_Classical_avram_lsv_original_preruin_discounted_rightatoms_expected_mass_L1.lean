-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
-- name    : AvramDividend.Classical.avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:09:09.52471+00:00
-- url     : https://prove2.me/theorems/abafc351-4cb0-4ab3-9c8a-f4d8e1696ccb
-- title:
--   Original true-ruin-stopped discounted physical right-dividend finite-grid L1 expected mass bound
-- statement:
--   On the actual original Brownian nondegenerate spectrally negative Levy source and actual original dividend strategy, the discounted sum of all physical right-dividend atoms before the original ruin-bounded stopping time on any finite strictly increasing deterministic mesh is integrable. Its expectation is bounded by the expected initial capital plus original finite-horizon Levy running supremum. This is a source-specific integrable expected mass result needed for Gaussian prepayment postpayment mesh convergence, without assuming post-ruin bounds or an external Poisson construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_preruin_discounted_grid_rightatoms_runningSup_bound
import Theorems.Thm_AvramDividend_Classical_avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_lsv_original_preruin_discounted_rightatoms_expected_mass_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (s : ℕ → ℝ≥0) (hstrict : ∀ i, s i < s (i + 1))
    (m : ℕ) (hbound : ∀ i ∈ Finset.range m, s i ≤ n)
    (q : ℝ) (hq : 0 ≤ q) :
    let A : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range m,
        if s i < ρ ω then
          Real.exp (-(q * (s i : ℝ))) *
            (rightLimit D (s i) ω - D (s i) ω)
        else 0
    Integrable A P ∧
      (∫ ω, A ω ∂P) ≤
        ∫ ω, x + runningSup X n ω ∂P := by sorry
