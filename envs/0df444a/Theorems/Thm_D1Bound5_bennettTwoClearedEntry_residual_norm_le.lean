-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_residual_norm_le
-- name    : D1Bound5.bennettTwoClearedEntry_residual_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:33:11.81391+00:00
-- url     : https://prove2.me/theorems/ba703f72-5562-41af-8e93-94fc9ea6844a
-- title:
--   Bennett Two Cleared Entry residual norm le
-- statement:
--   The actual integral two-anchor Q-matrix satisfies the manuscript's Gamma residual bound. All factors are constructed entries; no approximation or contour bound is provided as a hypothesis.
-- source:
--   D1Bound5/BennettTwoResidualBound.lean, lines 21-85, SHA-256 ca93022505dbc1c4d74fe949e488db6dcf4bf0f1cbebbd1635b2a6e0bdfce03a. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.bennettTwoClearedEntry_residual_norm_le
    (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1 < ‖a‖ * ‖c‖)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖∑ j, bennettTwoClearedEntry a b c k i j *
        (1 + bennettTwoNodes a b j * (a * b * c)⁻¹) ^ (1 / 2 : ℂ)‖ ≤
      (4 * ‖a - b‖ ^ 2 / (‖a‖ * ‖b‖ * ‖c‖ ^ 2)) ^ k *
        (Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
          (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))) /
            (1 - 1 / (‖a‖ * ‖c‖)) ^ (2 * (k : ℝ) - 1 / 2) := by sorry

end D1Bound5
end
