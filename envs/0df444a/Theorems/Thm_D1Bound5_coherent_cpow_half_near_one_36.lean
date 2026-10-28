-- Prove2me | Theorems.Thm_D1Bound5_coherent_cpow_half_near_one_36
-- name    : D1Bound5.coherent_cpow_half_near_one_36
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:10.909031+00:00
-- url     : https://prove2.me/theorems/1a4123d5-57a3-448a-8b96-f98e99d2aa97
-- title:
--   Coherent cpow half near one 36
-- statement:
--   The broader near-one estimates needed by the general three-anchor lemma. The analytic branch is fixed by the convergent binomial series.
-- source:
--   D1Bound5/CoherentThreeGeneral.lean, lines 7-58, SHA-256 3d70781b1840256782f08bbde98695e566d97e604c0ab97a7731d5a9f2432486. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherent_cpow_half_near_one_36
    (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ ≤ (1 / 36 : ℝ)) :
    (35 / 36 : ℝ) < ‖(1 + w) ^ (1 / 2 : ℂ)‖ ∧
    ‖(1 + w) ^ (1 / 2 : ℂ)‖ < (37 / 36 : ℝ) ∧
    ‖1 - (1 + w) ^ (1 / 2 : ℂ)‖ < (36 / 71 : ℝ) * ‖w‖ := by sorry









end D1Bound5
end
