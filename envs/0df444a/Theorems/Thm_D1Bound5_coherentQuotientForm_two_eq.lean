-- Prove2me | Theorems.Thm_D1Bound5_coherentQuotientForm_two_eq
-- name    : D1Bound5.coherentQuotientForm_two_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:21:02.003478+00:00
-- url     : https://prove2.me/theorems/63a7daed-7b8c-48a6-b6a9-5c6dd832652b
-- title:
--   Coherent Quotient Form two eq
-- statement:
--   The quotient-weighted two-anchor form is exactly the difference of its two actual coherent anchor roots and its terminal-root term.
-- source:
--   D1Bound5/CoherentTwoGap.lean, lines 10-24, SHA-256 9b03b858f3c9928eaa8ca4f9e63d4ac4f91f397c8d8e6a3896dbdcf15993ec4f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.coherentQuotientForm_two_eq
    (a : Fin 2 → ℂ) (hinj : Function.Injective a) (p q eta : ℂ) :
    coherentQuotientForm a (a 0 - a 1) p q eta =
      coherentAnchorRoot (a 0) p q eta - coherentAnchorRoot (a 1) p q eta -
        (a 0 - a 1) * coherentTerminalRoot p q eta := by sorry





end D1Bound5
end
