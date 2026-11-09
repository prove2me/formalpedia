-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_initial_event_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_original_finitegrid_initial_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T14:04:12.350662+00:00
-- url     : https://prove2.me/theorems/ad485084-3245-443e-9582-041cb10e84bb
-- title:
--   Original full-cutoff compensated negative-jump finite grid has zero mean on every initial event
-- statement:
--   The previously proved original physical full-cutoff predictable finite-grid compensation integrates to zero against every event in the initial right-continuous sigma algebra. Filtration monotonicity promotes that event to each grid cell. The statement is directly suitable for an original stopped pure-jump initial-event expected budget.
-- source:
--   UBV-JUMP11 full-cutoff finite-grid upgrade of public Proved 5ebeb352, removing an unnecessary explicit measurability premise at each grid cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finitegrid_past_event_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ubv_jump11_original_finitegrid_initial_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
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
    let Z : ℕ → Ω → ℝ := fun i ω => H i ω * ((N i ω).toReal - r i)
    (∫ ω in A, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by sorry
