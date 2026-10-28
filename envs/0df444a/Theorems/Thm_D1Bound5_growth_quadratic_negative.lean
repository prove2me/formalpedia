-- Prove2me | Theorems.Thm_D1Bound5_growth_quadratic_negative
-- name    : D1Bound5.growth_quadratic_negative
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:13.338005+00:00
-- url     : https://prove2.me/theorems/b05053d3-09c5-4486-afe7-33cba979a73e
-- title:
--   Growth quadratic negative
-- statement:
--   Exact real endpoint estimates behind Lemma irregular-growth.
-- source:
--   D1Bound5/IrregularGrowth.lean, lines 83-108, SHA-256 f449e549f059d0b5ff8d04afd421d9f1c8ec2bba64f1395f4efdedd79016bf4d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
open scoped NumberField
open Module

namespace D1Bound5








theorem _root_.D1Bound5.growth_quadratic_negative (A B C : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B)
    (hBC : B ≤ C) (hC : C ≤ 2*A*B) :
    (A+B+C+1)^2+4-4*A*B*C < 0 := by sorry





end D1Bound5
end
