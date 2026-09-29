-- Prove2me | solution 1 for flt5_coprime_sum_phi5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:20:11.823284+00:00
-- url     : https://prove2.me/submissions/82cb6c2c-93cb-45c1-b53a-af7bcaf48b76

import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) :
    (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = c ^ 5 :=
  (by ring : (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) =
      a ^ 5 + b ^ 5).trans h_eq
