-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_renewal_exact_atom_from_atomless_powers
-- name    : AvramDividend.Classical.geometric_renewal_exact_atom_from_atomless_powers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:26:29.433038+00:00
-- url     : https://prove2.me/theorems/72e0151a-a27a-464f-a7e1-e28744619e95
-- title:
--   Exact zero-atom coefficient of an atomless higher-order geometric renewal measure
-- statement:
--   A geometric renewal measure has a Dirac mass in its zeroth summand. If all subsequent measures assign zero mass to that same point, the full sum has exactly the zeroth coefficient as its point mass. This sharpens the established positive-atom lemma and supplies the precise bounded-variation scale normalisation after convolution powers are shown atomless.
-- source:
--   Existing Proved positive_atom_geometric_measure_sum (7be6625f-2197-48ab-b916-5154e32e0c58), canonical Esscher scale representation (bd5082fb-392c-4e36-9858-95c79a31ed92), and measure-sum identity.

import Theorems.Thm_AvramDividend_Classical_positive_atom_geometric_measure_sum
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.geometric_renewal_exact_atom_from_atomless_powers
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : ℕ → Measure α) (c : ℝ≥0∞) (x : α)
    (hm0 : m 0 = Measure.dirac x)
    (hpositive : ∀ n : ℕ, 0 < n → m n {x} = 0) :
    (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)) {x} = c := by sorry
