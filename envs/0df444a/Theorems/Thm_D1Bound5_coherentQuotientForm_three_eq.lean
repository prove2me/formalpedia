-- Prove2me | Theorems.Thm_D1Bound5_coherentQuotientForm_three_eq
-- name    : D1Bound5.coherentQuotientForm_three_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:28:51.556896+00:00
-- url     : https://prove2.me/theorems/3856cdd8-2684-4203-ad1e-15303f33c51e
-- title:
--   Coherent Quotient Form three eq
-- statement:
--   The quotient expression has exactly the integral polynomial weights used in the common-quadratic argument.
-- source:
--   D1Bound5/CoherentThreeSimultaneous.lean, lines 135-151, SHA-256 ee201a480813e6432c988412c0b0b54c06b4815f872ad14ff04a828a0dbc941f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions

section
open Finset Polynomial

namespace D1Bound5
















theorem _root_.D1Bound5.coherentQuotientForm_three_eq
    (a : Fin 3 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ) :
    coherentQuotientForm a (coherentVandermonde3 a) p q eta =
      -(a 0-a 1)*(a 0-a 2)*(a 1-a 2)*coherentTerminalRoot p q eta +
        a 0*(a 1-a 2)*coherentAnchorRoot (a 0) p q eta -
        a 1*(a 0-a 2)*coherentAnchorRoot (a 1) p q eta +
        a 2*(a 0-a 1)*coherentAnchorRoot (a 2) p q eta := by sorry

end D1Bound5
end
