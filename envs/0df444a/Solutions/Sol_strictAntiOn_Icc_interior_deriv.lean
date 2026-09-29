-- Prove2me | solution 1 for strictAntiOn_Icc_interior_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T20:22:27.566918+00:00
-- url     : https://prove2.me/submissions/a99b27c7-941a-4976-a0a8-04762dbdfe39

import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set

theorem solution
    (f f' : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Set.Ioo a b, f' x < 0) :
    StrictAntiOn f (Set.Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) hcont
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]
  exact hneg x hx
