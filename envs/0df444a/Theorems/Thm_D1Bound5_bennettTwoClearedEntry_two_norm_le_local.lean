-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_two_norm_le_local
-- name    : D1Bound5.bennettTwoClearedEntry_two_norm_le_local
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:35:34.793009+00:00
-- url     : https://prove2.me/theorems/d322d2e7-86ba-45d1-8978-5327c351baeb
-- title:
--   Bennett Two Cleared Entry two norm le local
-- statement:
--   Actual column two of the integral Q-matrix obeys the same estimate at the other interpolation node.
-- source:
--   D1Bound5/BennettTwoEntryBounds.lean, lines 32-55, SHA-256 14876837f679d01eed3a777728ec991e30224838aed15293edc00f667fea9a45. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.bennettTwoClearedEntry_two_norm_le_local
    (a b c : ℂ) (k : ℕ) (hk : 1 ≤ k) (i : Fin 3)
    (r : ℝ) (hr : 0 < r) (hU : 0 < ‖a * b * c + a‖)
    (ha : 2 * r ≤ ‖a‖) (hab : 2 * r ≤ ‖a - b‖) :
    ‖bennettTwoClearedEntry a b c k i 2‖ ≤
      (4 * ‖a‖ * ‖b‖ * ‖a - b‖ ^ 2) ^ k *
        ((‖a * b * c + a‖ + r) / ‖a * b * c + a‖) *
          ((‖a * b * c + a‖ + r) /
            (r * (‖a‖ - r) * (‖a - b‖ - r))) ^ k := by sorry

end D1Bound5
end
