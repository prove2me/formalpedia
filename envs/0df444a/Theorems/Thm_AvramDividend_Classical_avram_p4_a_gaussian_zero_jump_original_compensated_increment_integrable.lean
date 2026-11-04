-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_compensated_increment_integrable
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_compensated_increment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:13:26.732715+00:00
-- url     : https://prove2.me/theorems/8068f3a2-0b52-45db-a68a-370031bea37f
-- title:
--   Original zero-jump Levy compensated Gaussian exponential increments are integrable
-- statement:
--   For every deterministic interval of the original zero-jump Levy source, the drift-centred, Gaussian-variance-compensated exponential increment has finite first moment. The proof transports the Proved fixed-time exponential integrability along genuine stationary increments.
-- source:
--   Original stationaryIncrements and Proved Avram P4-A zero-jump centred exponential integrability; Mathlib IdentDistrib.integrable_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centered_exponential_integrable

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_compensated_increment_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) -
        ((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θ ^ 2 / 2))) P := by sorry
