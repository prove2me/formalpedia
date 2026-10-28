-- Prove2me | Theorems.Thm_D1Bound5_oneSmallFixedRows_metadata
-- name    : D1Bound5.oneSmallFixedRows_metadata
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:47.373435+00:00
-- url     : https://prove2.me/theorems/14e1bea2-ff05-439c-b7cb-64ea1e58aa91
-- title:
--   One Small Fixed Rows metadata
-- statement:
--   Exact metadata used when joining the finite fourth-entry certificates to the analytic retained-triple argument. Every assertion is checked directly on all 56 manuscript rows.
-- source:
--   D1Bound5/OneSmallRowMetadata.lean, lines 6-16, SHA-256 afdd76e66b529f3c4affc34d0fa9a5c63fb42757c91e1d7293941c1072281505. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt


theorem _root_.D1Bound5.oneSmallFixedRows_metadata :
    ∀ r ∈ oneSmallFixedRows,
      1024 ≤ r.cutoff ∧
      (r.anchorA.norm = 1 ∨ r.anchorA.norm = 2) ∧
      9 ≤ r.anchorB.norm ∧
      (r.anchorA.norm = 2 →
        4*r.anchorA.norm*r.anchorB.norm*r.anchorS.norm < r.cutoff) := by sorry

end D1Bound5
end
