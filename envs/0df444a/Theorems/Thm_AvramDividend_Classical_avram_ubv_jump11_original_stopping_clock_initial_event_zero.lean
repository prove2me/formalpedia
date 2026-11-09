-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_stopping_clock_initial_event_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_stopping_clock_initial_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T14:35:43.318944+00:00
-- url     : https://prove2.me/theorems/20e8f56d-ff76-4a8d-a60c-69b4585afeb3
-- title:
--   Original physical negative-jump compensator has zero initial-event expectation when masked by a stopping clock
-- statement:
--   For the same original spectrally negative Lévy path and its right-continuous filtration, negative-jump compensated counts stopped by survival of an original stopping time have zero expected value over every initial event. The actual stopping time supplies predictability of the physical cell masks; no independent process or auxiliary distribution is assumed.
-- source:
--   Original initial-event compensation ad485084; physical stopping time measurability. Directly reusable with sigma_k of pure-jump source 71fd10ee.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_initial_event_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ubv_jump11_original_stopping_clock_initial_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω in A, ∑ i ∈ Finset.range n,
      (if grid i < τ ω then (1 : ℝ) else 0) *
        ((N i ω).toReal - r i) ∂P) = 0 := by sorry
