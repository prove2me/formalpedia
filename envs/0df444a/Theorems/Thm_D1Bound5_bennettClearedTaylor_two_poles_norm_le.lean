-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_norm_le
-- name    : D1Bound5.bennettClearedTaylor_two_poles_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:27:50.497994+00:00
-- url     : https://prove2.me/theorems/14b76d4e-f860-49f0-83cf-2a0e4daebc99
-- title:
--   Bennett Cleared Taylor two poles norm le
-- statement:
--   The extra row pole cancels the coefficient radius, yielding a uniform bound for every actual row. The condition 2r≤both distances holds at r=2u/5.
-- source:
--   D1Bound5/BennettLocalCoefficientBound.lean, lines 44-92, SHA-256 fd4a0f2effe871e8ebc1c24036cd22f28f05f6913ef472311d8f40670735ea89. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.bennettClearedTaylor_two_poles_norm_le
    (a N d e : ℂ) (k d0 d1 d2 : ℕ) (hk : 1 ≤ k)
    (hrow : d0 + d1 + d2 = 1)
    (r : ℝ) (hr : 0 < r) (hU : 0 < ‖N + a‖)
    (hd : 2 * r ≤ ‖d‖) (he : 2 * r ≤ ‖e‖) :
    ‖(bennettClearedTaylor k (k + d0 - 1) (1 / 2 : ℂ) a
      (bennettPoleSeries d (k + d1) * bennettPoleSeries e (k + d2))).eval N‖ ≤
      ((‖N + a‖ + r) / ‖N + a‖) *
        ((‖N + a‖ + r) / (r * (‖d‖ - r) * (‖e‖ - r))) ^ k := by sorry

end D1Bound5
end
