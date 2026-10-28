-- Prove2me | Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_1_4
-- name    : D1Bound5.firstPairGeometryRowsAt_covers_1_4
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:42:37.591681+00:00
-- url     : https://prove2.me/theorems/26baa627-8865-483f-81ea-156d8deac27e
-- title:
--   First Pair Geometry Rows At covers 1 4
-- statement:
--   Auxiliary result `firstPairGeometryRowsAt_covers_1_4` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairGeometryData.lean, lines 425-427, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002

section
namespace D1Bound5
open QuadInt



namespace FirstPairGeometryRow






























end FirstPairGeometryRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000

























































































































































































theorem _root_.D1Bound5.firstPairGeometryRowsAt_covers_1_4 :
    firstPairRepresentatives_1_4 ⊆ (firstPairGeometryRowsAt 1 4).toFinset := by sorry





end D1Bound5
end
