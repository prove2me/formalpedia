-- Prove2me | Theorems.Thm_D1Bound5_quadInt_norm_add_le_twice
-- name    : D1Bound5.quadInt_norm_add_le_twice
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:13.29415+00:00
-- url     : https://prove2.me/theorems/d68d38e9-752a-4591-93c8-8163f2e10a17
-- title:
--   Quad Int norm add le twice
-- statement:
--   The norm parallelogram identity gives a division-free root bound.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 12-21, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.quadInt_norm_add_le_twice {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (x y : QuadInt tau nu) :
    (x+y).norm ≤ 2*x.norm+2*y.norm := by sorry































end D1Bound5
end
