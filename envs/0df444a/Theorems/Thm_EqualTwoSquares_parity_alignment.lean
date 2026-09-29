-- Prove2me | Theorems.Thm_EqualTwoSquares_parity_alignment
-- name    : EqualTwoSquares.parity_alignment
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:25:58.723381+00:00
-- url     : https://prove2.me/theorems/09931270-bd7e-4a0b-8d32-e41d6c52633f
-- title:
--   Parity alignment after at most one interchange of the right-hand entries
-- statement:
--   Let a, b, c and d be integers with a^2 + b^2 = c^2 + d^2. Then either a - c and b - d are both even, or a - d and b - c are both even. Equivalently, either a agrees with c modulo 2 and b agrees with d modulo 2, or the same holds after c and d are interchanged.
-- source:
--   Mission target; no machine-checked proof yet.

import Mathlib

namespace EqualTwoSquares

/-- Objective 4, parity: after possibly swapping c and d, matching entries have equal parity. -/
theorem parity_alignment {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (Even (a - c) ∧ Even (b - d)) ∨ (Even (a - d) ∧ Even (b - c)) := by sorry

end EqualTwoSquares
