-- Prove2me | Theorems.Thm_D1Bound5_oneSmallCutoffRows_triples
-- name    : D1Bound5.oneSmallCutoffRows_triples
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:14:57.598069+00:00
-- url     : https://prove2.me/theorems/51a71117-354a-4163-9c2b-ae59ca88a8a3
-- title:
--   One Small Cutoff Rows triples
-- statement:
--   The arithmetic rows cover exactly the 56 finite-table triples and the separate rational triple (1,3,8), with their printed cutoffs.
-- source:
--   D1Bound5/OneSmallCutoffArithmetic.lean, lines 563-569, SHA-256 d65ab45ed304589ddbe969477a809953ce44ed6ceae42c0145a3b1e641e229f4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt



namespace OneSmallCutoffRow



























end OneSmallCutoffRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0










































































































































































































































theorem _root_.D1Bound5.oneSmallCutoffRows_triples :
    (oneSmallCutoffRows.map OneSmallCutoffRow.triple).toFinset =
      insert (⟨0,1,(1,0),(3,0),(8,0),1024⟩ : OneSmallTripleRow)
        oneSmallFixedRows := by sorry



end D1Bound5
end
