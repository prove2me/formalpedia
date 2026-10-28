-- Prove2me | Theorems.Thm_D1Bound5_firstPairGeometryRows_valid
-- name    : D1Bound5.firstPairGeometryRows_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:11:30.525532+00:00
-- url     : https://prove2.me/theorems/c05e7ab8-7a4f-4886-b3c0-e6940391823b
-- title:
--   First Pair Geometry Rows valid
-- statement:
--   Auxiliary result `firstPairGeometryRows_valid` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairGeometryData.lean, lines 347-391, SHA-256 ca79ea3d5261caa9f78a67579ed8bf7ee86ad2bdfe411217ba297b1a793cea9a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002

section
namespace D1Bound5
open QuadInt



namespace FirstPairGeometryRow






























end FirstPairGeometryRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000







































































































































































theorem _root_.D1Bound5.firstPairGeometryRows_valid (r : FirstPairGeometryRow)
    (hr : r ∈ firstPairGeometryRows) : r.Valid := by sorry























end D1Bound5
end
