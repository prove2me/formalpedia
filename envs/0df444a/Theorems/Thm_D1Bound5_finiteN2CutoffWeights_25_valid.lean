-- Prove2me | Theorems.Thm_D1Bound5_finiteN2CutoffWeights_25_valid
-- name    : D1Bound5.finiteN2CutoffWeights_25_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:19.98942+00:00
-- url     : https://prove2.me/theorems/962fb51a-57e2-4057-a921-b0e46bd76af3
-- title:
--   N₂ coefficient bound for oneSmallCutoffRow_25
-- statement:
--   The rational weights `finiteN2CutoffWeights_25` give an evaluated N₂ coefficient certificate for cutoff row `oneSmallCutoffRow_25`. All weights are nonnegative, every coefficient norm satisfies its prescribed weighted bound, and each row’s total weight, multiplied by 101/100, is strictly less than the row’s bound M₂.
-- source:
--   D1Bound5/OneSmallN2FixedArithmetic.lean, lines 215-217, SHA-256 164624a5c23628e859c312cd4e25138d33e47f04cca6c8177425d4c89d42a3cd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions

section
namespace D1Bound5
open QuadInt







set_option maxRecDepth 100000
set_option maxHeartbeats 0







































































































theorem _root_.D1Bound5.finiteN2CutoffWeights_25_valid :
    FiniteN2FixedBound oneSmallCutoffRow_25 finiteN2CutoffWeights_25 := by sorry































































































































end D1Bound5
end
