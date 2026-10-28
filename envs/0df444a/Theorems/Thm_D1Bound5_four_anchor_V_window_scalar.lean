-- Prove2me | Theorems.Thm_D1Bound5_four_anchor_V_window_scalar
-- name    : D1Bound5.four_anchor_V_window_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:21.556322+00:00
-- url     : https://prove2.me/theorems/998eea0c-653f-4541-9dbe-6dec39bf2948
-- title:
--   Four anchor V window scalar
-- statement:
--   A convenient smaller closed V window, with rational coefficients 101 and 2/5. The strict actual form estimate excludes its endpoints.
-- source:
--   D1Bound5/FourAnchorVWindow.lean, lines 10-39, SHA-256 745b5229447b46b23cd565d6e05245ce882a6a77d258e5d7beee2c8be63afe71. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.four_anchor_V_window_scalar
    (A B T P Q Z : ℝ) (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hP : 0 < P) (hZ : 0 < Z)
    (hlo : (1-1/4000 : ℝ)*P*Q ≤ Z^2)
    (hhi : Z^2 ≤ (1+1/4000 : ℝ)*P*Q)
    (hform : 1 < 5*B*T^2/Z+3*T*Z/(4*A*P^3)) :
    Q < 101*B^2*T^4/P ∨ (2/5 : ℝ)*A^2*P^5/T^2 < Q := by sorry



end D1Bound5
end
