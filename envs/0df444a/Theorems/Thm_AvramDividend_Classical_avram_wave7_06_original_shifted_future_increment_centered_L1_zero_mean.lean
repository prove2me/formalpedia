-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_shifted_future_increment_centered_L1_zero_mean
-- name    : AvramDividend.Classical.avram_wave7_06_original_shifted_future_increment_centered_L1_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:35:14.438009+00:00
-- url     : https://prove2.me/theorems/ccf62912-3db0-426b-9e78-865089a09bf8
-- title:
--   Original shifted future Lévy increment centred by its source mean is L¹ and zero-mean
-- statement:
--   If X_t is P-integrable, every actual source future increment X_(s+t)-X_s minus the original mean E[X_t] is P-integrable and has mean zero. The original process's probability field makes the expectation of the constant equal itself. This is the correct original-filtration scalar compensation interface; it is not a statement about a marked jump sum.
-- source:
--   W7-06 source future increment L¹ centring as a finite-horizon martingale-difference precursor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_shifted_future_increment_centered_L1_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    Integrable
      (fun ω => X.X (s + t) ω - X.X s ω -
        (∫ ω, X.X t ω ∂P)) P ∧
    (∫ ω, X.X (s + t) ω - X.X s ω -
      (∫ η, X.X t η ∂P) ∂P) = 0 := by sorry
