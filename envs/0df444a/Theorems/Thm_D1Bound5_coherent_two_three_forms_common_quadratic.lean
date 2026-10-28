-- Prove2me | Theorems.Thm_D1Bound5_coherent_two_three_forms_common_quadratic
-- name    : D1Bound5.coherent_two_three_forms_common_quadratic
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:35:54.957163+00:00
-- url     : https://prove2.me/theorems/75d1cc58-5bc6-4768-8cbf-a89a7aa7102e
-- title:
--   Coherent two three forms common quadratic
-- statement:
--   Two vanishing coherent triple forms sharing their first two roots produce one quadratic taking all four prescribed values. Only the difference of the two shared anchors is divided out.
-- source:
--   D1Bound5/CoherentThreeSimultaneous.lean, lines 20-47, SHA-256 ee201a480813e6432c988412c0b0b54c06b4815f872ad14ff04a828a0dbc941f. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Finset Polynomial

namespace D1Bound5








theorem _root_.D1Bound5.coherent_two_three_forms_common_quadratic
    {F : Type*} [Field F] (a R : Fin 4 → F) (z : F) (hab : a 0 ≠ a 1)
    (h2 : -(a 0-a 1)*(a 0-a 2)*(a 1-a 2)*z +
      a 0*(a 1-a 2)*R 0 - a 1*(a 0-a 2)*R 1 + a 2*(a 0-a 1)*R 2 = 0)
    (h3 : -(a 0-a 1)*(a 0-a 3)*(a 1-a 3)*z +
      a 0*(a 1-a 3)*R 0 - a 1*(a 0-a 3)*R 1 + a 3*(a 0-a 1)*R 3 = 0) :
    ∃ v w : F, ∀ i, z * (a i)^2 + v * a i + w = a i * R i := by sorry









end D1Bound5
end
