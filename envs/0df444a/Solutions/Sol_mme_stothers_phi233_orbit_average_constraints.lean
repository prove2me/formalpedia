-- Prove2me | solution 1 for mme_stothers_phi233_orbit_average_constraints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:11:59.919073+00:00
-- url     : https://prove2.me/submissions/8d5951f0-5f78-424f-b097-e927d9d56445

import Mathlib.Tactic

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (x : Fin 10 → ℝ) (sigma mu : ℝ)
    (htotal : ∑ r : Fin 10, x r = 1)
    (hsigma0 : x 0 + x 1 + x 2 = sigma / 2)
    (hsigma2 : x 7 + x 8 + x 9 = sigma / 2)
    (hmuJ0 : x 3 + x 7 = mu / 2)
    (hmuJ3 : x 2 + x 6 = mu / 2)
    (hmuK0 : x 6 + x 9 = mu / 2)
    (hmuK3 : x 0 + x 3 = mu / 2) :
    let a := (x 0 + x 2 + x 7 + x 9) / 2
    let b := x 1 + x 8
    let c := x 3 + x 6
    let d := x 4 + x 5
    2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu := by
  have htotal' := htotal
  simp [Fin.sum_univ_succ] at htotal'
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  · linarith
