-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_integral_summand_zero
-- name    : D1Bound5.bennett_two_integral_summand_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:39.023988+00:00
-- url     : https://prove2.me/theorems/216e2cd0-9ad4-410f-b50e-249238856073
-- title:
--   Bennett two integral summand zero
-- statement:
--   The actual column-zero residue summand, with all binomial factors and pole signs, is integral in every subring containing the anchor entries.
-- source:
--   D1Bound5/BennettTwoIntegralSummands.lean, lines 8-34, SHA-256 cf848c27c1e7b66b43f1bb2e9f008252599e35de774adedcbacb56ab48e836d3. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.bennett_two_integral_summand_zero (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (k d0 d1 d2 h0 h1 h2 : ℕ) (hk : 1 ≤ k)
    (hd : d0 + d1 + d2 = 1) (hh : h0 + h1 + h2 + 1 = k + d0) :
    ∃ q ∈ S,
      (((4 : F) ^ k * Ring.choose ((k : F) + 1 / 2) h0) *
        Ring.choose (-((k + d1 : ℕ) : F)) h1 *
        Ring.choose (-((k + d2 : ℕ) : F)) h2) *
      ((a * b * (a - b) ^ 2) ^ k * (a * b * c) ^ (k - h0) *
        ((-b)⁻¹) ^ (k + d1 + h1) * ((-a)⁻¹) ^ (k + d2 + h2)) = 1 * q := by sorry





end D1Bound5
end
