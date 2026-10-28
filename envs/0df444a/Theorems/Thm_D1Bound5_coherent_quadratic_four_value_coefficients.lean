-- Prove2me | Theorems.Thm_D1Bound5_coherent_quadratic_four_value_coefficients
-- name    : D1Bound5.coherent_quadratic_four_value_coefficients
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:15.243969+00:00
-- url     : https://prove2.me/theorems/8b5bb1ca-f7e5-400a-b47a-6c695eb3a679
-- title:
--   Coherent quadratic four value coefficients
-- statement:
--   Four distinct prescribed product-square values determine the three lower coefficients of the monic quartic. This is the algebraic core of simultaneous triple-form nonvanishing.
-- source:
--   D1Bound5/CoherentThreeSimultaneous.lean, lines 49-92, SHA-256 ee201a480813e6432c988412c0b0b54c06b4815f872ad14ff04a828a0dbc941f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_CoherentThreeSimultaneous_Definitions

section
open Finset Polynomial

namespace D1Bound5










theorem _root_.D1Bound5.coherent_quadratic_four_value_coefficients
    {F : Type*} [Field F] (a R : Fin 4 → F) (hinj : Function.Injective a)
    (p q z v w : F) (hz : z^2 = p*q+1)
    (hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1))
    (hJ : ∀ i, z*(a i)^2+v*a i+w = a i*R i) :
    w^2 = coherentElementary4 a ∧
    2*v*w = -coherentElementary3 a ∧
    v^2+2*z*w-1 = coherentElementary2 a := by sorry







end D1Bound5
end
