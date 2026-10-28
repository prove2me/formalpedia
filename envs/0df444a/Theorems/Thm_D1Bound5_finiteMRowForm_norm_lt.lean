-- Prove2me | Theorems.Thm_D1Bound5_finiteMRowForm_norm_lt
-- name    : D1Bound5.finiteMRowForm_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:24.150052+00:00
-- url     : https://prove2.me/theorems/6b16cdd5-a96d-4f7f-b06a-e2a3db85d89f
-- title:
--   Finite MRow Form norm lt
-- statement:
--   Transfer the actual ordinary-three order-two residual to the original integral row, using its proved finite coefficient height.
-- source:
--   D1Bound5/FiniteMRowBound.lean, lines 49-92, SHA-256 8f362cf2cd05cc79c68cd55d4cd481a8f4757c97b8b62b056279ef4736669437. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
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
import Definitions.Def_D1Bound5_FiniteMIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteMRowBound_Definitions

section
namespace D1Bound5








theorem _root_.D1Bound5.finiteMRowForm_norm_lt
    (a b s c z rA rB rS : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hC : 1 ≤ ‖c‖) (hAC : 1000 ≤ ‖a‖*‖c‖)
    (herr : ∀ j : Fin 3,
      ‖(1+1/(finiteMAnchors a b s j*c))^(1/2 : ℂ)-
        ![rA,rB,rS] j/(finiteMAnchors a b s j*z)‖ ≤
          (3/2 : ℝ)*‖c‖/(‖finiteMAnchors a b s j‖*‖z‖^2)) (i : Fin 4) :
    ‖finiteMRowForm a b s c z rA rB rS i‖ <
      (8/9 : ℝ)*608^2*‖b‖^3*‖s‖^8*‖c‖^3/‖z‖+
        (3920/81 : ℝ)*‖b‖^2*‖s‖^5*‖z‖/(‖a‖^3*‖c‖^6) := by sorry

end D1Bound5
end
