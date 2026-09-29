-- Prove2me | Theorems.Thm_EqualTwoSquares_sum_sq_eq_halves
-- name    : EqualTwoSquares.sum_sq_eq_halves
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:26:11.694985+00:00
-- url     : https://prove2.me/theorems/ee3071e6-eb29-4c3c-b9b4-9241d48556d1
-- title:
--   Under parity alignment the equation becomes XY = UV
-- statement:
--   Let a, b, c and d be integers with a^2 + b^2 = c^2 + d^2, and suppose that a - c and b - d are even. Then there are integers X, Y, U and V with X + Y = a, X - Y = c, U - V = b, U + V = d and X * Y = U * V.
-- source:
--   Mission target; no machine-checked proof yet.

import Mathlib

namespace EqualTwoSquares

/-- Objective 4, substitution: under parity alignment the equation becomes XY = UV. -/
theorem sum_sq_eq_halves {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2)
    (hac : Even (a - c)) (hbd : Even (b - d)) :
    ∃ X Y U V : ℤ,
      X + Y = a ∧ X - Y = c ∧ U - V = b ∧ U + V = d ∧ X * Y = U * V := by sorry

end EqualTwoSquares
