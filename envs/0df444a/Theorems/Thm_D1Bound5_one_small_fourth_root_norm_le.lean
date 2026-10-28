-- Prove2me | Theorems.Thm_D1Bound5_one_small_fourth_root_norm_le
-- name    : D1Bound5.one_small_fourth_root_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:31.016809+00:00
-- url     : https://prove2.me/theorems/5420d6f3-8758-4962-9df0-25d820f356a1
-- title:
--   One small fourth root norm le
-- statement:
--   A uniform root bound for all 56 fourth-entry certificates.
-- source:
--   D1Bound5/OneSmallFiniteCheck.lean, lines 35-48, SHA-256 071c08b2bdc31b423cf7fceaeeb7fd97f8c1844d2c362578eed3d43c62423b55. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt




theorem _root_.D1Bound5.one_small_fourth_root_norm_le {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a z q : QuadInt tau nu)
    (ha : a.norm ≤ 2) (hz : z.norm ≤ 21270) (hq : q*q = a*z+1) :
    q.norm ≤ 300 := by sorry



















end D1Bound5
end
