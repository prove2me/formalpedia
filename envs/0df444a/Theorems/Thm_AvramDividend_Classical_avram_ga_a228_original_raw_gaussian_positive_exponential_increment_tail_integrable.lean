-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a228_original_raw_gaussian_positive_exponential_increment_tail_integrable
-- name    : AvramDividend.Classical.avram_ga_a228_original_raw_gaussian_positive_exponential_increment_tail_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T01:00:00.553588+00:00
-- url     : https://prove2.me/theorems/8c0ec3a3-53c3-4b66-b1fd-cec40a613b8f
-- title:
--   Actual original Gaussian raw positive exponential increment threshold tail integrable
-- statement:
--   The one-sided positive exponential tail of the genuine raw Gaussian Lévy increment X_t-X_s is integrable over every deterministic bounded interval for all nonnegative exponential tilts. The exact raw increment equals sigma times the centred-normalised Gaussian increment plus the deterministic original Lévy drift. The result supplies the missing unconditional raw-cell integrability needed for original a226 and a216.
-- source:
--   Original zerojump Gaussian source a68 plus exact raw drift reconstruction

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a228_original_raw_gaussian_positive_exponential_increment_tail_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ δ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      let R : ℝ := X.X t ω - X.X s ω
      if δ ≤ R then Real.exp (θ * R) else 0) P := by sorry
