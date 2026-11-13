-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a29_original_interval_lindeberg_tail
-- name    : AvramDividend.Classical.avram_ga_a29_original_interval_lindeberg_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:51:31.806559+00:00
-- url     : https://prove2.me/theorems/cfcfcf23-4c09-42c7-8e9c-8d226361328e
-- title:
--   Original Gaussian deterministic-interval large quadratic increment tail has O(h squared) bound
-- statement:
--   For genuine centred Gaussian increments of the original process on a deterministic interval, quadratic energy at magnitude exceeding r has expectation bounded by 3 times the interval duration squared divided by r squared, after sigma normalisation.
-- source:
--   Gaussian A original X/P stopped Taylor Lindeberg route for b0d9951c, using ga_a27 and be3f4cbc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_lindeberg_scalar_fourth_energy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a29_original_interval_lindeberg_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
    (hMeasZ : Measurable (fun ω : Ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : Ω → ℝ := fun ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
    (∫⁻ ω, ENNReal.ofReal (if r ≤ |Z ω| then (Z ω) ^ 2 else 0) ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2)) := by sorry
