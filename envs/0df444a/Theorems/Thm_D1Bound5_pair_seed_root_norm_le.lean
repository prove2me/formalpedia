-- Prove2me | Theorems.Thm_D1Bound5_pair_seed_root_norm_le
-- name    : D1Bound5.pair_seed_root_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:21:05.490761+00:00
-- url     : https://prove2.me/theorems/cd29224f-7552-4710-9d2e-1e2a9864e1a7
-- title:
--   Pair seed root norm le
-- statement:
--   Every root needed for the radius-33 seed search has norm at most 132. This deliberately loose bound keeps the finite search small and uniform.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 23-37, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.pair_seed_root_norm_le {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a z q : QuadInt tau nu)
    (ha : a.norm ≤ 8) (hz : z.norm ≤ 1089) (hq : q*q = a*z+1) :
    q.norm ≤ 132 := by sorry





























end D1Bound5
end
