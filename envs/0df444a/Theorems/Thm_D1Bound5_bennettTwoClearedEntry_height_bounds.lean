-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_height_bounds
-- name    : D1Bound5.bennettTwoClearedEntry_height_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:44.643011+00:00
-- url     : https://prove2.me/theorems/f1d97f6b-e376-439f-a6d6-8e704c7ca740
-- title:
--   Bennett Two Cleared Entry height bounds
-- statement:
--   Actual uniform entry bounds at every positive order. The positive-series proof absorbs its small numerator loss into the paper's rounding to42 and thus obtains the slightly stronger bounds without the prefactor p2.
-- source:
--   D1Bound5/BennettTwoHeightBounds.lean, lines 14-77, SHA-256 fdaa812fbb34a8a666e2436a20b9c6dd6a699844aa0547a9a65c1f759aa97515. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.bennettTwoClearedEntry_height_bounds
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖ * ‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖bennettTwoClearedEntry a b c k i 1‖ < (42 * ‖a‖ ^ 2 * ‖b‖ * ‖c‖) ^ k ∧
    ‖bennettTwoClearedEntry a b c k i 2‖ < (42 * ‖b‖ ^ 3 * ‖c‖) ^ k := by sorry

end D1Bound5
end
