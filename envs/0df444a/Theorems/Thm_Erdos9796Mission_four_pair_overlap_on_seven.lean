-- Prove2me | Theorems.Thm_Erdos9796Mission_four_pair_overlap_on_seven
-- name    : Erdos9796Mission_four_pair_overlap_on_seven
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-07T21:33:36.075718+00:00
-- url     : https://prove2.me/theorems/9bd194e6-8fc5-4637-8f3c-71645a468443
-- title:
--   Four two-point supports in a seven-point set
-- statement:
--   Let U be a finite set with at most seven elements, and let A, B, C, D be two-element subsets of U. Suppose A and B are disjoint, A and C are disjoint, and C and D are disjoint. Then at least one of A ∩ D, B ∩ C, or B ∩ D is nonempty.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/39000ab545ab30982e92d70f8ab7ef0c21fa4b00/lean/Erdos9796Proof/P97/FourPairCoverage.lean — Problem97.FourPairCoverage.overlap_of_three_disjoint_pairs

import Mathlib.Data.Finset.Card
set_option autoImplicit false

theorem Erdos9796Mission_four_pair_overlap_on_seven {α : Type*} [DecidableEq α]
    (U A B C D : Finset α) (hU : U.card ≤ 7)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hCU : C ⊆ U) (hDU : D ⊆ U)
    (hA : A.card = 2) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hCD : Disjoint C D) :
    (A ∩ D).Nonempty ∨ (B ∩ C).Nonempty ∨ (B ∩ D).Nonempty := by sorry
