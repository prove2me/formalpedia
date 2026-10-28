-- Prove2me | Theorems.Thm_D1Bound5_finiteM_residual_norm_lt_point
-- name    : D1Bound5.finiteM_residual_norm_lt_point
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:34:10.999995+00:00
-- url     : https://prove2.me/theorems/2c4e378c-aa2e-4671-b25c-be8946831341
-- title:
--   Finite M residual norm lt point
-- statement:
--   The exact order-eight residual zero gives a C^-6 bound for the constructed order-two M family, before the row-factor geometry is bounded.
-- source:
--   D1Bound5/FiniteMResidualPoint.lean, lines 38-133, SHA-256 f7bb209498622e9e35161ef7d6d2d014918b6ada1ab43bba06f6efcfedaca12e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteMResidualPoint_Definitions

section
open Finset Polynomial

namespace D1Bound5










theorem _root_.D1Bound5.finiteM_residual_norm_lt_point (a b s c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hAC : 1000 ≤ ‖a‖*‖c‖) (i : Fin 4) :
    ‖finiteMResidual a b s c i‖ <
      (101/100 : ℝ)*(45/2048)*(‖a-b‖*‖a-s‖*‖b-s‖)^4 /
        (‖a‖^2*‖b‖^2*‖s‖^2*‖c‖^6*‖finiteMRowFactor a b s i‖) := by sorry

end D1Bound5
end
