-- Prove2me | Theorems.Thm_D1Bound5_extension_coarse_quadratic
-- name    : D1Bound5.extension_coarse_quadratic
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:09.08756+00:00
-- url     : https://prove2.me/theorems/8b209756-73f4-4773-a486-191afa545276
-- title:
--   Extension coarse quadratic
-- statement:
--   The coarser quadratic used to exclude B <= C <= 2AB.
-- source:
--   D1Bound5/IrregularGrowth.lean, lines 39-61, SHA-256 f449e549f059d0b5ff8d04afd421d9f1c8ec2bba64f1395f4efdedd79016bf4d. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.extension_coarse_quadratic (a b c u v : ℂ)
    (hs : u+v = 2*(a+b+(1+2*a*b)*c))
    (hp : u*v = regularDefect a b c) (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    0 ≤ (‖a‖+‖b‖+‖c‖+1)^2+4-4*‖a‖*‖b‖*‖c‖ := by sorry









end D1Bound5
end
