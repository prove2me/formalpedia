-- Prove2me | Theorems.Thm_D1Bound5_bennettResidueTaylor_coeff_mul_binomial
-- name    : D1Bound5.bennettResidueTaylor_coeff_mul_binomial
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:34:09.72158+00:00
-- url     : https://prove2.me/theorems/a57b406c-beb5-4b11-94a6-52d5e39e781a
-- title:
--   Bennett Residue Taylor coeff mul binomial
-- statement:
--   Multiplying the actual local residue polynomial by its binomial series transfers each coefficient to the residue of a polynomial monomial.
-- source:
--   D1Bound5/BennettResidualCancellation.lean, lines 13-53, SHA-256 0e8f4d1dac16aef29c7622ad8fa6e48d05646e38a9ebaf133da673991996797d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]


theorem _root_.D1Bound5.bennettResidueTaylor_coeff_mul_binomial (k t r : ℕ) (ht : t ≤ k)
    (ν a : F) (B : PowerSeries F) :
    PowerSeries.coeff r
      ((bennettResidueTaylor k t ν a B : PowerSeries F) *
        PowerSeries.rescale a (PowerSeries.binomialSeries F ν)) =
      Ring.choose ((k : F) + ν) r *
        PowerSeries.coeff t (((PowerSeries.C a + PowerSeries.X) ^ r) * B) := by sorry

section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]











end Nodes

end D1Bound5
end
