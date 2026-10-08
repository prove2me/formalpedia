-- Prove2me | solution 1 for fare_abs_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:18:29.277356+00:00
-- url     : https://prove2.me/submissions/0e411ca5-0b5c-46a7-91ee-063749ab15cf

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (f : ℕ → ℝ) (k j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    |f j| ≤ ∑ i ∈ Finset.Icc 1 k, |f i| := by
  exact Finset.single_le_sum
    (s := Finset.Icc 1 k)
    (f := fun i => |f i|)
    (fun i _ => abs_nonneg (f i))
    (Finset.mem_Icc.mpr ⟨hj, hjk⟩)
