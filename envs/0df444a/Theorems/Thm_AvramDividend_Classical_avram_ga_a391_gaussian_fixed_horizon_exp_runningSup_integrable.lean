-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
-- name    : AvramDividend.Classical.avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T14:24:26.937769+00:00
-- url     : https://prove2.me/theorems/4fc6190c-3e6a-4198-8638-346670b55a87
-- title:
--   Gaussian fixed-horizon exponential running supremum is integrable
-- statement:
--   For a nondegenerate Gaussian spectrally negative Lévy source, every nonnegative-rate exponential of the finite-horizon running supremum is Bochner-integrable.
-- source:
--   The Proved avram_ga_a40 fixed horizon exponential lintegral, the Proved joint measurability of runningSup; reusable a387 one-sided strict crossing envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hSigma : 0 < X.σ)
    (n : ℝ≥0) (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun ω : Ω => Real.exp (β * runningSup X n ω)) P := by sorry
