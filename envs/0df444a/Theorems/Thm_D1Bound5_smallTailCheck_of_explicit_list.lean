-- Prove2me | Theorems.Thm_D1Bound5_smallTailCheck_of_explicit_list
-- name    : D1Bound5.smallTailCheck_of_explicit_list
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:57:33.906637+00:00
-- url     : https://prove2.me/theorems/82d7d7fe-9116-448d-957f-8f3257c6dd7b
-- title:
--   Small Tail Check of explicit list
-- statement:
--   The explicit finite list covers the entire mathematical small-tail statement when it covers the closed disk. The list need not be minimal.
-- source:
--   D1Bound5/SmallTailExplicit.lean, lines 28-53, SHA-256 1276e7682da7a886b79eccc5e7267d374a94b67c65efc71b70ac09c8660526af. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FiniteTail_Definitions
import Definitions.Def_D1Bound5_SmallTailExplicit_Definitions

section
namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.smallTailCheck_of_explicit_list {tau nu : ℤ}
    (xs : List (QuadInt tau nu))
    (cover : ∀ z ∈ disk tau nu 15, z ∈ xs)
    (checked : tailListBool xs = true) : SmallTailCheck tau nu := by sorry

end D1Bound5
end
