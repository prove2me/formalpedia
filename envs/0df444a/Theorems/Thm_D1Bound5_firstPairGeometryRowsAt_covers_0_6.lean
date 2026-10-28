-- Prove2me | Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_0_6
-- name    : D1Bound5.firstPairGeometryRowsAt_covers_0_6
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:46:05.638884+00:00
-- url     : https://prove2.me/theorems/486168bd-90cf-441c-b2e3-d50e2b877cd4
-- title:
--   First Pair Geometry Rows At covers 0 6
-- statement:
--   Auxiliary result `firstPairGeometryRowsAt_covers_0_6` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairGeometryData.lean, lines 409-411, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a. Project: https://github.com/tomislav-math/d1-bound5-lean

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

















































































































































































theorem _root_.D1Bound5.firstPairGeometryRowsAt_covers_0_6 :
    firstPairRepresentatives_0_6 ⊆ (firstPairGeometryRowsAt 0 6).toFinset := by sorry













end D1Bound5
end
