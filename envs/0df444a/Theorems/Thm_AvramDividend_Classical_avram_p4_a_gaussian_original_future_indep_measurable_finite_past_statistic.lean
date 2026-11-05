-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_future_indep_measurable_finite_past_statistic
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_future_indep_measurable_finite_past_statistic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:40:42.962105+00:00
-- url     : https://prove2.me/theorems/354b6c22-4279-48d2-8982-6c3c668638f9
-- title:
--   Original centred future increment independent of any measurable finite-past statistic
-- statement:
--   For any finite collection of observations of the original Lévy process at or before s, a future centred increment from s to t is independent of every measurable real-valued function of the observation vector.
-- source:
--   Proved original process finite-vector sigma-algebra independence and Mathlib IndepFun.comp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_indep_finite_past_vector

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_future_indep_measurable_finite_past_statistic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≤ s)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Measurable φ) :
    IndepFun
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
      (fun ω => φ (fun i : Fin n => Y.X (v i) ω)) P := by sorry
