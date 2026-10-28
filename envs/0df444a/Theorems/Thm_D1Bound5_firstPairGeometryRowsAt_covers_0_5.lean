-- Prove2me | Theorems.Thm_D1Bound5_firstPairGeometryRowsAt_covers_0_5
-- name    : D1Bound5.firstPairGeometryRowsAt_covers_0_5
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:47:31.474169+00:00
-- url     : https://prove2.me/theorems/5dc9b9a6-5335-4a32-a7df-b935796b0bad
-- title:
--   First Pair Geometry Rows At covers 0 5
-- statement:
--   Auxiliary result `firstPairGeometryRowsAt_covers_0_5` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairGeometryData.lean, lines 405-407, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a. Project: https://github.com/tomislav-math/d1-bound5-lean

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















































































































































































theorem _root_.D1Bound5.firstPairGeometryRowsAt_covers_0_5 :
    firstPairRepresentatives_0_5 ⊆ (firstPairGeometryRowsAt 0 5).toFinset := by sorry















end D1Bound5
end
