-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_residual_norm_lt_half_rate
-- name    : D1Bound5.bennettTwoClearedEntry_residual_norm_lt_half_rate
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:23:30.33408+00:00
-- url     : https://prove2.me/theorems/aba8f1d8-54ed-4312-8c0e-c6ad1377d342
-- title:
--   Bennett Two Cleared Entry residual norm lt half rate
-- statement:
--   Final residual inequality for every actual row of the integral Q-matrix, with exactly the manuscript's rate R2 and factor one half.
-- source:
--   D1Bound5/BennettTwoResidualRate.lean, lines 85-97, SHA-256 a959de125fdeac3f4cd04800acc29e3af47d9b0e2de609a39d3e257a4ba1c377. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions

section
namespace D1Bound5












theorem _root_.D1Bound5.bennettTwoClearedEntry_residual_norm_lt_half_rate
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1 < ‖a‖ * ‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖∑ j, bennettTwoClearedEntry a b c k i j *
        (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)‖ <
      1 / (2 * (bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖) ^ k) := by sorry

end D1Bound5
end
