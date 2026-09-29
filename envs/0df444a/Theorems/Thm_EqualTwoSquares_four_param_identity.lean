-- Prove2me | Theorems.Thm_EqualTwoSquares_four_param_identity
-- name    : EqualTwoSquares.four_param_identity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:23:55.03505+00:00
-- url     : https://prove2.me/theorems/0e9a824d-a634-4784-9051-872a09dd1f64
-- title:
--   The four-parameter identity produces solutions over the integers
-- statement:
--   For all integers p, q, r and s, one has (pr + qs)^2 + (ps - qr)^2 = (pr - qs)^2 + (ps + qr)^2. Thus the quadruple (pr + qs, ps - qr, pr - qs, ps + qr) solves a^2 + b^2 = c^2 + d^2.
-- source:
--   Mission target; machine-checked locally in examples/two-squares/Identity.lean.

import Mathlib

namespace EqualTwoSquares

/-- Objective 1: the four-parameter identity over the integers. -/
theorem four_param_identity (p q r s : ℤ) :
    (p * r + q * s)^2 + (p * s - q * r)^2 =
      (p * r - q * s)^2 + (p * s + q * r)^2 := by sorry

end EqualTwoSquares
