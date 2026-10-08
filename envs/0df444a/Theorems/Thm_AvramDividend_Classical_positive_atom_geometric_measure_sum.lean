-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_atom_geometric_measure_sum
-- name    : AvramDividend.Classical.positive_atom_geometric_measure_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:28:40.729705+00:00
-- url     : https://prove2.me/theorems/7be6625f-2197-48ab-b916-5154e32e0c58
-- title:
--   A geometric measure sum with a Dirac zeroth term has a positive atom
-- statement:
--   Let m_n be positive measures and suppose m_0 is the Dirac mass at x. If c>0, then the geometric measure sum Σ_n c^(n+1) m_n has strictly positive mass at {x}. The n=0 term alone contributes c, and every other term is nonnegative.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.MeasureSpace theorem Measure.le_sum and MeasureTheory.Measure.Dirac evaluation lemmas. This generic measure lemma supplies the atom-at-zero hypothesis for the bounded-variation renewal measure β = Σ n, δ^(-(n+1)) κ_a^{*n}, whose zeroth convolution power is Dirac 0.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical

/-- A countable geometric sum of positive measures has positive mass at a point
whenever its zeroth measure is a Dirac mass there and the coefficient is positive. -/
theorem positive_atom_geometric_measure_sum
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : ℕ → Measure α) (c : ℝ≥0∞) (hc : 0 < c) (x : α)
    (hm0 : m 0 = Measure.dirac x) :
    0 < (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)) {x} := by
  sorry

end AvramDividend.Classical
