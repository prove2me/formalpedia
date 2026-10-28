-- Prove2me | Theorems.Thm_D1Bound5_FirstPairGeometryMatches_residual_rates
-- name    : D1Bound5.FirstPairGeometryMatches.residual_rates
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:11:48.879066+00:00
-- url     : https://prove2.me/theorems/d60c232d-f871-4ee3-bbcc-9afc9f6bb4da
-- title:
--   First Pair Geometry Matches — residual rates
-- statement:
--   The pair-dependent residual coefficients agree exactly. The P rate uses a different geometric enclosure and is deliberately not identified.
-- source:
--   D1Bound5/FirstPairFixedTransfer.lean, lines 18-29, SHA-256 3faa8c267acd6dc418ad7dfd9d428a018612986ed715dc34ae106ea4a4b160f1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001

section
namespace D1Bound5




theorem _root_.D1Bound5.FirstPairGeometryMatches.residual_rates
    (g : FirstPairGeometryRow) (r : OneSmallCutoffRow)
    (h : FirstPairGeometryMatches g r) :
    g.R2 = r.R2 ∧ g.Rn = r.Rn ∧ g.R3 = r.R3 ∧
      g.R4 = r.R4 ∧ g.R5 = r.R5 := by sorry

end D1Bound5
end
