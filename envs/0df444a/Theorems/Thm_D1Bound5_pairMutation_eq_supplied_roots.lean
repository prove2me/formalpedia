-- Prove2me | Theorems.Thm_D1Bound5_pairMutation_eq_supplied_roots
-- name    : D1Bound5.pairMutation_eq_supplied_roots
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:53.006991+00:00
-- url     : https://prove2.me/theorems/19a2cb5b-5c91-4f97-9b09-7f0e561f8c4e
-- title:
--   Pair Mutation eq supplied roots
-- statement:
--   Both original deterministic neighbors are among the supplied-root mutations. Canonical roots occur only in this symbolic soundness proof.
-- source:
--   D1Bound5/PairClosureWitness.lean, lines 76-90, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62. Project: https://github.com/tomislav-math/d1-bound5-lean

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














theorem _root_.D1Bound5.pairMutation_eq_supplied_roots {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b z r0 r s : QuadInt tau nu)
    (h0 : r0 * r0 = a * b + 1) (hr : r * r = a * z + 1)
    (hs : s * s = b * z + 1) {w : QuadInt tau nu}
    (hw : w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z) :
    w = mutate a b z r0 r s ∨ w = mutate a b z r0 r (-s) := by sorry







end D1Bound5
end
