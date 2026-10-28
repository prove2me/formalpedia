-- Prove2me | Theorems.Thm_D1Bound5_irregular_growth
-- name    : D1Bound5.irregular_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:15:28.960994+00:00
-- url     : https://prove2.me/theorems/f391b8e5-971a-4a2d-8163-cc4a3df94143
-- title:
--   Irregular growth
-- statement:
--   Lemma irregular-growth in the full ring of every imaginary quadratic field. Ordered moduli may be equal.
-- source:
--   D1Bound5/IrregularGrowth.lean, lines 133-158, SHA-256 f449e549f059d0b5ff8d04afd421d9f1c8ec2bba64f1395f4efdedd79016bf4d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Regular_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5












theorem _root_.D1Bound5.irregular_growth {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (hK : finrank ℚ K = 2) (φ : K →+* ℂ)
    (a b c r s t : 𝓞 K) (hr : r^2 = a*b+1) (hs : s^2 = a*c+1)
    (ht : t^2 = b*c+1) (hi : regularDefect a b c ≠ 0)
    (hA : 3 ≤ ‖φ (a : K)‖) (hAB : ‖φ (a : K)‖ ≤ ‖φ (b : K)‖)
    (hBC : ‖φ (b : K)‖ ≤ ‖φ (c : K)‖) :
    2*‖φ (a : K)‖*‖φ (b : K)‖ < ‖φ (c : K)‖ := by sorry

end D1Bound5
end
