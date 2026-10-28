-- Prove2me | Theorems.Thm_D1Bound5_pairSeedsCovered_of_checked
-- name    : D1Bound5.pairSeedsCovered_of_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:36:59.580354+00:00
-- url     : https://prove2.me/theorems/b04aa35e-6cd1-4f60-972c-a10ec19c5c5d
-- title:
--   Pair Seeds Covered of checked
-- statement:
--   Mathematical soundness of the root-based finite seed certificate.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 72-87, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt














theorem _root_.D1Bound5.pairSeedsCovered_of_checked {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hNa : a.norm ≤ 8)
    (roots vertices : List (QuadInt tau nu))
    (hcover : ∀ q ∈ disk tau nu 132, q ∈ roots)
    (hcheck : pairSeedsCoveredBool a b roots vertices = true)
    (z : QuadInt tau nu) (hz : PairExtension a b z) (hNz : z.norm ≤ 1089) :
    z ∈ vertices := by sorry





















end D1Bound5
end
