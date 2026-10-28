-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_integral_summand_one
-- name    : D1Bound5.bennett_two_integral_summand_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:22.871505+00:00
-- url     : https://prove2.me/theorems/927f42b4-5a88-472b-8215-b8eb04d51a6c
-- title:
--   Bennett two integral summand one
-- statement:
--   The actual column-one residue summand is divisible by `a^k` inside every subring containing the anchors.
-- source:
--   D1Bound5/BennettTwoIntegralSummands.lean, lines 36-62, SHA-256 cf848c27c1e7b66b43f1bb2e9f008252599e35de774adedcbacb56ab48e836d3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]




theorem _root_.D1Bound5.bennett_two_integral_summand_one (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hb0 : b ≠ 0) (hab : a ≠ b)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d1) :
    ∃ q ∈ S,
      (((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h1) *
        Ring.choose (-((k + d0 : ℕ) : F)) h0 *
        Ring.choose (-((k + d2 : ℕ) : F)) h2) *
      ((a * b * (a - b) ^ 2) ^ k * (a * b * c + b) ^ (k - h1) *
        (b⁻¹) ^ (k + d0 + h0) * ((b - a)⁻¹) ^ (k + d2 + h2)) = a ^ k * q := by sorry



end D1Bound5
end
