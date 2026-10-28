-- Prove2me | Theorems.Thm_D1Bound5_finiteP_half_coefficients
-- name    : D1Bound5.finiteP_half_coefficients
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:03.786563+00:00
-- url     : https://prove2.me/theorems/c28e9f20-2cae-4a10-a465-0624a6b6ff45
-- title:
--   Finite P half coefficients
-- statement:
--   Auxiliary result `finiteP_half_coefficients` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FinitePResidualIdentity.lean, lines 11-27, SHA-256 72e3fea4ae1d93b79c83366074679f850f075659fb82a9a62794934f87487052. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

theorem _root_.D1Bound5.finiteP_half_coefficients :
    halfBinomialCoeff 5 = 7/256 ∧ halfBinomialCoeff 6 = -21/1024 ∧
    halfBinomialCoeff 7 = 33/2048 := by sorry

































end D1Bound5
end
