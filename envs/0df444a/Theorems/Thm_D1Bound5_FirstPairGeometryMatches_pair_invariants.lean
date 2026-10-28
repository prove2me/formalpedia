-- Prove2me | Theorems.Thm_D1Bound5_FirstPairGeometryMatches_pair_invariants
-- name    : D1Bound5.FirstPairGeometryMatches.pair_invariants
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:46:03.962208+00:00
-- url     : https://prove2.me/theorems/93129ee9-d759-4814-9dad-3360e7374bc0
-- title:
--   First Pair Geometry Matches — pair invariants
-- statement:
--   Matching coordinate pairs have identical exact squared norms and separation, even though the unused third coordinate differs.
-- source:
--   D1Bound5/FirstPairFixedTransfer.lean, lines 5-16, SHA-256 3faa8c267acd6dc418ad7dfd9d428a018612986ed715dc34ae106ea4a4b160f1. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.FirstPairGeometryMatches.pair_invariants
    (g : FirstPairGeometryRow) (r : OneSmallCutoffRow)
    (h : FirstPairGeometryMatches g r) :
    g.a0 = r.a0 ∧ g.b0 = r.b0 ∧ g.dab = r.dab := by sorry



end D1Bound5
end
