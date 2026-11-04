-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:26:36.402214+00:00
-- url     : https://prove2.me/theorems/3526c4e3-b634-4738-80db-002649f32a4d
-- title:
--   Original same-volatility normalised Gaussian increment exponential is integrable
-- statement:
--   For same-volatility original sources X and zero-jump Y, every positive-parameter exponential of the centred increment divided by the original source volatility is integrable. No auxiliary Brownian process is involved.
-- source:
--   Proved P4-A fixed-time normalised exponential integrability and source stationaryIncrements; Mathlib IdentDistrib.integrable_iff.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ))) P := by sorry
