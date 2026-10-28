-- Prove2me | Theorems.Thm_D1Bound5_finiteQ_half_coefficients
-- name    : D1Bound5.finiteQ_half_coefficients
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:04.144586+00:00
-- url     : https://prove2.me/theorems/4468c785-95f4-4ed1-96f7-2c4a46bce192
-- title:
--   Finite Q half coefficients
-- statement:
--   Auxiliary result `finiteQ_half_coefficients` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteQResidualIdentity.lean, lines 9-28, SHA-256 74ab040376af9b42e7ee62656f2fd8f3a92a0111248e8b31465d43a74a137c58. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5

theorem _root_.D1Bound5.finiteQ_half_coefficients :
    halfBinomialCoeff 0 = 1 ∧ halfBinomialCoeff 1 = 1/2 ∧
    halfBinomialCoeff 2 = -1/8 ∧ halfBinomialCoeff 3 = 1/16 ∧
    halfBinomialCoeff 4 = -5/128 := by sorry









end D1Bound5
end
