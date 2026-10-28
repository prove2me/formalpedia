-- Prove2me | Theorems.Thm_D1Bound5_pairSeedCandidate_eq
-- name    : D1Bound5.pairSeedCandidate_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:38:11.520863+00:00
-- url     : https://prove2.me/theorems/5f520ae8-8adc-4ab3-b05f-52c9e7373c5b
-- title:
--   Pair Seed Candidate eq
-- statement:
--   Every actual extension is reconstructed from either chosen square root.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 46-61, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt










theorem _root_.D1Bound5.pairSeedCandidate_eq {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a z q : QuadInt tau nu)
    (ha : a ≠ 0) (hq : q*q = a*z+1) : pairSeedCandidate a q = z := by sorry

























end D1Bound5
end
