-- Prove2me | Theorems.Thm_D1Bound5_monic_quadratic_neg_between
-- name    : D1Bound5.monic_quadratic_neg_between
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:24:59.469994+00:00
-- url     : https://prove2.me/theorems/df1c92bf-6300-41c7-91d0-9286c299986e
-- title:
--   Monic quadratic neg between
-- statement:
--   Strict negativity of a monic quadratic on a closed interval from its two endpoint values. This includes equality at either endpoint.
-- source:
--   D1Bound5/IrregularGrowth.lean, lines 63-81, SHA-256 f449e549f059d0b5ff8d04afd421d9f1c8ec2bba64f1395f4efdedd79016bf4d. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.monic_quadratic_neg_between (l u x b c : ℝ) (hlu : l < u)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : l^2+b*l+c < 0) (hu : u^2+b*u+c < 0) : x^2+b*x+c < 0 := by sorry







end D1Bound5
end
