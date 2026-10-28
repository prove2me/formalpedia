-- Prove2me | Theorems.Thm_D1Bound5_mutate_reverse_canonical
-- name    : D1Bound5.mutate_reverse_canonical
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:26:12.534972+00:00
-- url     : https://prove2.me/theorems/7811a67d-84ed-4142-ae8b-695f7922eaaa
-- title:
--   Mutate reverse canonical
-- statement:
--   Every mutation edge can be reversed using one of the two canonical neighbors of its target, regardless of the original root signs.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 139-161, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions

section
namespace D1Bound5
open QuadInt


























theorem _root_.D1Bound5.mutate_reverse_canonical {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (a b z r0 r s : QuadInt tau nu)
    (h0 : r0*r0 = a*b+1) (hr : r*r = a*z+1) (hs : s*s = b*z+1) :
    z = pairMutationPlus a b (mutate a b z r0 r s) ∨
    z = pairMutationMinus a b (mutate a b z r0 r s) := by sorry









end D1Bound5
end
