-- Prove2me | Theorems.Thm_EqualTwoSquares_complete_parametrization
-- name    : EqualTwoSquares.complete_parametrization
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:23:27.969505+00:00
-- url     : https://prove2.me/theorems/5e2fbf33-6086-49c4-a894-d49d3616bc96
-- title:
--   Every integer solution of a^2+b^2=c^2+d^2 comes from four parameters
-- statement:
--   Let a, b, c and d be integers with a^2 + b^2 = c^2 + d^2. Then there are integers p, q, r and s with a = pr + qs, b = ps - qr, c = pr - qs and d = ps + qr; alternatively, there are integers p, q, r and s with a = pr + qs, b = ps - qr, d = pr - qs and c = ps + qr, i.e. the same conclusion holds after the two entries on the right-hand side are interchanged.
-- source:
--   Mission target; no machine-checked proof yet.

import Mathlib

namespace EqualTwoSquares

/-- Objective 6, the goal: the four-parameter parametrisation is complete. -/
theorem complete_parametrization {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (∃ p q r s : ℤ,
      a = p * r + q * s ∧ b = p * s - q * r ∧
        c = p * r - q * s ∧ d = p * s + q * r) ∨
      (∃ p q r s : ℤ,
        a = p * r + q * s ∧ b = p * s - q * r ∧
          d = p * r - q * s ∧ c = p * s + q * r) := by sorry

end EqualTwoSquares
