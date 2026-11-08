-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_original_stop_coefficient_L2_energy_convergence
-- name    : AvramDividend.Classical.avram_ubv_gaussian15_original_stop_coefficient_L2_energy_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:15:45.728087+00:00
-- url     : https://prove2.me/theorems/b4d5a2b3-50bf-4334-b4d2-d9ceb32f6dfc
-- title:
--   Original stopped Gaussian expected-square error tends to zero with predictable coefficient energy
-- statement:
--   With the original ν=0 Lévy process, unchanged P and 𝓕.rightCont, and one genuinely bounded stopping time τ, convergence in integrated coefficient-square error for original-history predictable weights implies convergence to zero of the expected square of the physical weighted stopped Gaussian increment error. This is the quantitative source-exact stability of one stochastic-integral cell, requiring no alternative Gaussian model, no assumed terminal integral and no jump compensation.
-- source:
--   Direct use of Proved original stopped Gaussian two-weight bracket identity 32c723fe and continuity of real multiplication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_original_stopped_two_weights_gaussian_bracket

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian15_original_stop_coefficient_L2_energy_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G : ℕ → Ω → ℝ) (H : Ω → ℝ)
    (hG : ∀ n,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G n))
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : ∀ n, Measurable (G n))
    (hHglobal : Measurable H)
    (hCoeff : Tendsto (fun n =>
      ∫ ω, (G n ω - H ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      ((G n ω - H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P)
      atTop (𝓝 0) := by sorry
