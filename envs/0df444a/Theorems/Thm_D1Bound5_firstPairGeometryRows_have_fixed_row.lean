-- Prove2me | Theorems.Thm_D1Bound5_firstPairGeometryRows_have_fixed_row
-- name    : D1Bound5.firstPairGeometryRows_have_fixed_row
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:27.11718+00:00
-- url     : https://prove2.me/theorems/c3c59616-053c-4a11-8c3f-64caa14c8e59
-- title:
--   First Pair Geometry Rows have fixed row
-- statement:
--   Auxiliary result `firstPairGeometryRows_have_fixed_row` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/FirstPairGeometryFixedRows.lean, lines 266-311, SHA-256 84225093eb3f30b90e3cc61b11e72d39cd0cb1bab3442a3d330db9c6b02d9f97. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002
import Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002

section
namespace D1Bound5





set_option maxRecDepth 100000
set_option maxHeartbeats 0



















































































theorem _root_.D1Bound5.firstPairGeometryRows_have_fixed_row (g : FirstPairGeometryRow)
    (hg : g ∈ firstPairGeometryRows) :
    ∃ r ∈ oneSmallCutoffRows, FirstPairGeometryMatches g r := by sorry

end D1Bound5
end
