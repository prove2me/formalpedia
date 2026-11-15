-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
-- name    : AvramDividend.Classical.avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:59:11.827139+00:00
-- url     : https://prove2.me/theorems/9792564b-59a9-4b49-9bb8-39b48a9b49bf
-- title:
--   Centred zero-jump Gaussian Lévy path has an integrable finite-horizon squared uniform supremum bound
-- statement:
--   For any finite time horizon, there exists an integrable random variable that bounds the squared centred Gaussian Lévy path uniformly over all times in the horizon almost surely.
-- source:
--   Standard continuous Brownian martingale maximal L² inequality; needed for Gaussian original full-cell uniform quadratic integrable majorant a397.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (T : ℝ≥0) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      (∀ᵐ ω ∂P, 0 ≤ S ω ∧
        ∀ t : ℝ≥0, t ≤ T →
          (X.X t ω - (t : ℝ) * X.c)^2 ≤ S ω) := by sorry
