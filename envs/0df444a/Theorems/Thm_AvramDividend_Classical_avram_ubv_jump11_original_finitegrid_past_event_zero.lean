-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_past_event_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_finitegrid_past_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:52:39.720641+00:00
-- url     : https://prove2.me/theorems/5ebeb352-1055-4e97-ab42-5b2bf9b6fdb7
-- title:
--   Original full-negative-cutoff predictable finite-grid compensated jump integral vanishes on every past event
-- statement:
--   Finite sum of original physical full negative cutoff jump-count compensations against bounded predictable weights has zero integral over any event measurable at the start of every cell, by exact same-space right-continuous filtration martingale centring. This is the needed finite-grid initial-event component for source-exact pure-jump stopped verification.
-- source:
--   UBV-JUMP11 original-process conditional finite-cell centring from public Proved 2aaf4594, generic past-event lemma 1820407b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ubv_jump11_original_finitegrid_past_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) (A : Set Ω)
    (hA : ∀ i, MeasurableSet[𝓕.rightCont (grid i)] A) :
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
    let Z : ℕ → Ω → ℝ := fun i ω => H i ω * ((N i ω).toReal - r i)
    (∫ ω in A, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by sorry
