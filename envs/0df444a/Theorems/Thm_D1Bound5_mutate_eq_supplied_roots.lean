-- Prove2me | Theorems.Thm_D1Bound5_mutate_eq_supplied_roots
-- name    : D1Bound5.mutate_eq_supplied_roots
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:34.581568+00:00
-- url     : https://prove2.me/theorems/ef1eea8d-fdac-4fb5-b798-529150c896c7
-- title:
--   Mutate eq supplied roots
-- statement:
--   Arbitrary genuine root choices give one of the two supplied-root mutations, including when one of the roots is zero.
-- source:
--   D1Bound5/PairClosureWitness.lean, lines 53-74, SHA-256 c3e5b89a544885205672d45a9a3cb231a99a79dcff6c62a96059e9f00b860a62. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
namespace D1Bound5
open QuadInt












theorem _root_.D1Bound5.mutate_eq_supplied_roots {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (a b z r0 r s R0 R S : QuadInt tau nu)
    (h0 : r0 * r0 = a * b + 1) (hr : r * r = a * z + 1)
    (hs : s * s = b * z + 1) (hR0 : R0 * R0 = a * b + 1)
    (hR : R * R = a * z + 1) (hS : S * S = b * z + 1) :
    mutate a b z R0 R S = mutate a b z r0 r s ∨
      mutate a b z R0 R S = mutate a b z r0 r (-s) := by sorry









end D1Bound5
end
