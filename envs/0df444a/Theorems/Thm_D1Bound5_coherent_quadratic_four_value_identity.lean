-- Prove2me | Theorems.Thm_D1Bound5_coherent_quadratic_four_value_identity
-- name    : D1Bound5.coherent_quadratic_four_value_identity
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:36:00.061949+00:00
-- url     : https://prove2.me/theorems/5bffb24f-3565-421b-b09b-842b92a3994a
-- title:
--   Coherent quadratic four value identity
-- statement:
--   Eliminating the two lower quadratic coefficients gives the exact rational identity used in the four-anchor contradiction.
-- source:
--   D1Bound5/CoherentThreeSimultaneous.lean, lines 94-115, SHA-256 ee201a480813e6432c988412c0b0b54c06b4815f872ad14ff04a828a0dbc941f. Project: https://github.com/tomislav-math/d1-bound5-lean

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












theorem _root_.D1Bound5.coherent_quadratic_four_value_identity
    (a R : Fin 4 → ℂ) (hinj : Function.Injective a) (ha : ∀ i, a i ≠ 0)
    (p q z v w : ℂ) (hz : z^2 = p*q+1)
    (hR : ∀ i, (R i)^2 = (a i*p+1)*(a i*q+1))
    (hJ : ∀ i, z*(a i)^2+v*a i+w = a i*R i) :
    p*q+1 =
      (coherentElementary2 a + 1 -
        (coherentElementary3 a)^2 / (4*coherentElementary4 a))^2 /
          (4*coherentElementary4 a) := by sorry





end D1Bound5
end
