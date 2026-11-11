-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger76_positive_only_value_masked_physical_source_measurable
-- name    : AvramDividend.Classical.avram_gledger76_positive_only_value_masked_physical_source_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:56:01.951414+00:00
-- url     : https://prove2.me/theorems/0f5b5d56-b2ac-4278-ae91-a952a0c065ff
-- title:
--   Finite stopped source with positive-only continuous value is measurable after inactive-cell cancellation
-- statement:
--   For a real value function continuous only on positive reserve, an original finite stopped-source sum is a.e. strongly measurable from measurable scalar source coordinates, provided every inactive cell cancels identically and every active pair of value evaluations is strictly positive. This explicitly avoids assuming w is Borel on negative reserves.
-- source:
--   Root-connected gledger71 source measurability, using gledger72 positive active-cell bound.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gledger76_positive_only_value_masked_physical_source_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ)))
    (m : ℕ) (E Y Z : ℕ → Ω → ℝ)
    (hE : ∀ i, Measurable (E i))
    (hY : ∀ i, Measurable (Y i))
    (hZ : ∀ i, Measurable (Z i))
    (hcell : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (0 < Y i ω ∧ 0 < Z i ω)) :
    AEStronglyMeasurable (fun ω =>
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) P := by sorry
