-- Prove2me | solution 1 for mme_finset_incidence_double_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:15:26.861867+00:00
-- url     : https://prove2.me/submissions/d282eef3-2837-469a-933a-c5a3d2285f05

import Mathlib

open BigOperators

set_option autoImplicit false

/-- Double-count a finite incidence relation by its two projections. -/
theorem solution
    {Ω A : Type} [DecidableEq Ω] [DecidableEq A]
    (W : Finset Ω) (U : Finset A) (P : Ω → A → Prop)
    [DecidableRel P] :
    (∑ ω ∈ W, (U.filter (P ω)).card) =
      ∑ a ∈ U, (W.filter (fun ω => P ω a)).card := by
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm
