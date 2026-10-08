-- Prove2me | solution 1 for fare_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:05:14.771491+00:00
-- url     : https://prove2.me/submissions/afabb05d-6f9f-489c-bb94-76eb654e0b71

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (f : ℕ → ℝ) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.Icc 1 k, |f i| :=
  Finset.sum_nonneg fun i hi => abs_nonneg (f i)
