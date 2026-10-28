-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_clear_column_one
-- name    : D1Bound5.bennett_two_clear_column_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:10.454466+00:00
-- url     : https://prove2.me/theorems/e6717195-251c-47e5-915d-8072f9a2675c
-- title:
--   Bennett two clear column one
-- statement:
--   Column one of the two-anchor construction. The exact remaining factor `a^k` is the column divisibility used by the arithmetic row-form argument.
-- source:
--   D1Bound5/BennettTwoDenominatorClearing.lean, lines 45-72, SHA-256 21eca1644697a9c747a683cd3c26583cb9a60c7838c517047d556b782f76b0da. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]






theorem _root_.D1Bound5.bennett_two_clear_column_one
    (a b c : F) (hb : b ≠ 0) (hab : a ≠ b)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d1) :
    (a * b * (a - b) ^ 2) ^ k * (a * b * c + b) ^ (k - h1) *
        (b⁻¹) ^ (k + d0 + h0) * ((a - b)⁻¹) ^ (k + d2 + h2) =
      a ^ k * (a * c + 1) ^ (k - h1) * b ^ (d2 + h2) *
        (a - b) ^ (k - (d2 + h2)) := by sorry







end D1Bound5
end
