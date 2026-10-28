-- Prove2me | Theorems.Thm_D1Bound5_three_general_window_scalar
-- name    : D1Bound5.three_general_window_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:32:02.224708+00:00
-- url     : https://prove2.me/theorems/4b39febe-63a9-48a4-9fc3-2c30936d434a
-- title:
--   Three general window scalar
-- statement:
--   Closed general-three forbidden interval, with slightly weaker rational endpoints so that all root errors are absorbed.
-- source:
--   D1Bound5/ThreeGeneralWindow.lean, lines 10-40, SHA-256 672e1e3d605f06db37de02cec597d627f04713038fc2c51993a56e88102920bc. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Positivity

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.three_general_window_scalar
    (A B S P Q Z : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 < S)
    (hP : 0 < P) (hZ : 0 < Z)
    (hlo : (1-1/4000 : ℝ)*P*Q ≤ Z^2)
    (hhi : Z^2 ≤ (1+1/4000 : ℝ)*P*Q)
    (hform : 1 < 5*B*S^2/Z+3*S*Z/(A*P^3)) :
    Q < 101*B^2*S^4/P ∨ A^2*P^5/(37*S^2) < Q := by sorry



end D1Bound5
end
