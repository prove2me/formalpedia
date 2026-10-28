-- Prove2me | solution 1 for finite_set_card_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:16:20.104144+00:00
-- url     : https://prove2.me/submissions/cc8c6923-b827-41cf-b348-b23bc284f0a0

import Mathlib

theorem solution
    {α : Type} [Fintype α]
    (A B : Set α)
    (hA : A.Finite) (hB : B.Finite)
    (hAB : A ⊆ B)
    (hcard : B.ncard ≤ A.ncard) :
    A = B :=
  Set.eq_of_subset_of_ncard_le hAB hcard hB
