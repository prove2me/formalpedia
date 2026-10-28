-- Prove2me | Theorems.Thm_D1Bound5_finiteM_residual_identity
-- name    : D1Bound5.finiteM_residual_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:46:27.950986+00:00
-- url     : https://prove2.me/theorems/da201f9f-49ec-474b-9f63-cd766c3208ad
-- title:
--   Finite M residual identity
-- statement:
--   Auxiliary result `finiteM_residual_identity` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FiniteMResidualPoint.lean, lines 25-36, SHA-256 f7bb209498622e9e35161ef7d6d2d014918b6ada1ab43bba06f6efcfedaca12e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteMBennettIdentity_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteMResidualPoint_Definitions

section
open Finset Polynomial

namespace D1Bound5







theorem _root_.D1Bound5.finiteM_residual_identity (a b s c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (i : Fin 4) :
    finiteMRowFactor a b s i * finiteMResidual a b s c i =
      ∑ j, finiteMBennettEntry a b s c i j *
        (1+finiteMNodes a b s j*(a*b*s*c)⁻¹)^(1/2 : ℂ) := by sorry



end D1Bound5
end
