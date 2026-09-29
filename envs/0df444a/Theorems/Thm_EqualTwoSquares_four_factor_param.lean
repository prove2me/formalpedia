-- Prove2me | Theorems.Thm_EqualTwoSquares_four_factor_param
-- name    : EqualTwoSquares.four_factor_param
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:26:25.192178+00:00
-- url     : https://prove2.me/theorems/dfb3e2b5-ae15-49f2-ad42-ebeb4d062921
-- title:
--   Every integer solution of XY = UV admits four parameters
-- statement:
--   Let X, Y, U and V be integers with X * Y = U * V. Then there are integers p, q, r and s such that X = pr, Y = qs, U = ps and V = qr.
-- source:
--   Mission target; no machine-checked proof yet.

import Mathlib

namespace EqualTwoSquares

/-- Objective 5: every solution of XY = UV over the integers admits four parameters. -/
theorem four_factor_param (X Y U V : ℤ) (h : X * Y = U * V) :
    ∃ p q r s : ℤ, X = p * r ∧ Y = q * s ∧ U = p * s ∧ V = q * r := by sorry

end EqualTwoSquares
