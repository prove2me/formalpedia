-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_clear_column_zero_signed
-- name    : D1Bound5.bennett_two_clear_column_zero_signed
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:49.413318+00:00
-- url     : https://prove2.me/theorems/c21bd0d0-979d-47a8-b30f-64e89bf4e351
-- title:
--   Bennett two clear column zero signed
-- statement:
--   Restoring the signs of the actual poles at zero.
-- source:
--   D1Bound5/BennettTwoDenominatorClearing.lean, lines 103-122, SHA-256 21eca1644697a9c747a683cd3c26583cb9a60c7838c517047d556b782f76b0da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]










theorem _root_.D1Bound5.bennett_two_clear_column_zero_signed
    (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d0) :
    (a * b * (a - b) ^ 2) ^ k * (a * b * c) ^ (k - h0) *
        ((-b)⁻¹) ^ (k + d1 + h1) * ((-a)⁻¹) ^ (k + d2 + h2) =
      (-1 : F) ^ ((k + d1 + h1) + (k + d2 + h2)) *
        (a ^ (d1 + h1) * b ^ (d2 + h2) * c ^ (k - h0) *
          (a - b) ^ (2 * k)) := by sorry



end D1Bound5
end
