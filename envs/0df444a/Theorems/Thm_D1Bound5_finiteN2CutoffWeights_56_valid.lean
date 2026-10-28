-- Prove2me | Theorems.Thm_D1Bound5_finiteN2CutoffWeights_56_valid
-- name    : D1Bound5.finiteN2CutoffWeights_56_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:12.168005+00:00
-- url     : https://prove2.me/theorems/2759fbe8-7e5e-485a-a1e4-6f4e91059222
-- title:
--   N₂ coefficient bound for oneSmallCutoffRow_56
-- statement:
--   The rational weights `finiteN2CutoffWeights_56` give an evaluated N₂ coefficient certificate for cutoff row `oneSmallCutoffRow_56`. All weights are nonnegative, every coefficient norm satisfies its prescribed weighted bound, and each row’s total weight, multiplied by 101/100, is strictly less than the row’s bound M₂.
-- source:
--   D1Bound5/OneSmallN2FixedArithmetic.lean, lines 432-434, SHA-256 164624a5c23628e859c312cd4e25138d33e47f04cca6c8177425d4c89d42a3cd. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions

section
namespace D1Bound5
open QuadInt







set_option maxRecDepth 100000
set_option maxHeartbeats 0



































































































































































































































theorem _root_.D1Bound5.finiteN2CutoffWeights_56_valid :
    FiniteN2FixedBound oneSmallCutoffRow_56 finiteN2CutoffWeights_56 := by sorry



end D1Bound5
end
