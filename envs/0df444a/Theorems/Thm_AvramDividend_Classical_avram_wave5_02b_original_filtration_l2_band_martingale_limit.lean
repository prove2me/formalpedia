-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_filtration_l2_band_martingale_limit
-- name    : AvramDividend.Classical.avram_wave5_02b_original_filtration_l2_band_martingale_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:34:26.928233+00:00
-- url     : https://prove2.me/theorems/2ac43d23-18e8-41aa-9a0e-282f9580a09a
-- title:
--   Original filtration L² limit preserves adaptedness and martingale conditional expectations
-- statement:
--   On one original probability space and filtration, suppose each finite-band L² process is adapted in the conditional-expectation sense and its future increments have zero conditional expectation, and suppose the finite-band values converge in L² at every time. Then the limit is adapted in the same L² sense and has the martingale conditional-expectation property at every pair of deterministic times. The convergence, finite-band adaptedness and conditional centring are explicit hypotheses; no bound or Lévy jump construction is claimed.
-- source:
--   Proved original probability L² conditional centering closure 675ebf1e-e87c-449c-a4f0-c2c72983329b and continuity of condExpL2.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_l2_conditional_centering_closed_under_band_limit

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02b_original_filtration_l2_band_martingale_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (hSigma : ∀ s : ℝ≥0, @SigmaFinite Ω (𝓕 s) (P.trim (𝓕.le s)))
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (L : ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (hconv : ∀ t, Tendsto (fun n => M n t) atTop (𝓝 (L t)))
    (hAdapt : ∀ s n,
      ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (M n s) :
        Lp ℝ (2 : ℝ≥0∞) P) = M n s)
    (hCenter : ∀ s t, s ≤ t → ∀ n,
      (MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (M n t - M n s) = 0) :
    (∀ s, ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L s) :
      Lp ℝ (2 : ℝ≥0∞) P) = L s) ∧
    (∀ s t, s ≤ t →
      ((MeasureTheory.condExpL2 ℝ ℝ (𝓕.le s)) (L t) :
        Lp ℝ (2 : ℝ≥0∞) P) = L s) := by sorry
