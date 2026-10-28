-- Prove2me | Theorems.Thm_D1Bound5_mutate_eq_canonical
-- name    : D1Bound5.mutate_eq_canonical
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:51.035602+00:00
-- url     : https://prove2.me/theorems/7742c65b-773f-45ee-9136-d8ebda02312a
-- title:
--   Mutate eq canonical
-- statement:
--   Arbitrary actual root choices give one of the two deterministic neighbors.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 119-137, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
























theorem _root_.D1Bound5.mutate_eq_canonical {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (a b z r0 r s : QuadInt tau nu)
    (h0 : r0*r0 = a*b+1) (hr : r*r = a*z+1) (hs : s*s = b*z+1) :
    mutate a b z r0 r s = pairMutationPlus a b z ∨
    mutate a b z r0 r s = pairMutationMinus a b z := by sorry











end D1Bound5
end
