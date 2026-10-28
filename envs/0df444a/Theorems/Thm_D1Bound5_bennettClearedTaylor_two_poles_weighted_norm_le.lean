-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_weighted_norm_le
-- name    : D1Bound5.bennettClearedTaylor_two_poles_weighted_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:27.516345+00:00
-- url     : https://prove2.me/theorems/4882f5ba-d4f9-47b9-b53e-a8c873713df7
-- title:
--   Bennett Cleared Taylor two poles weighted norm le
-- statement:
--   A genuine two-pole local Taylor coefficient is bounded by the positive generating-function majorant. No Cauchy coefficient estimate is assumed.
-- source:
--   D1Bound5/BennettLocalCoefficientBound.lean, lines 7-42, SHA-256 fd4a0f2effe871e8ebc1c24036cd22f28f05f6913ef472311d8f40670735ea89. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.bennettClearedTaylor_two_poles_weighted_norm_le
    (a N d e : ℂ) (k t p q : ℕ) (ht : t ≤ k)
    (r : ℝ) (hr : 0 ≤ r) (hU : 0 < ‖N + a‖)
    (hd : r < ‖d‖) (he : r < ‖e‖) :
    ‖(bennettClearedTaylor k t (1 / 2 : ℂ) a
      (bennettPoleSeries d p * bennettPoleSeries e q)).eval N‖ * r ^ t ≤
      ((‖N + a‖ + r) ^ (k + 1) / ‖N + a‖) *
        ((‖d‖ - r)⁻¹ ^ p * (‖e‖ - r)⁻¹ ^ q) := by sorry



end D1Bound5
end
