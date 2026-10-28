-- Prove2me | Theorems.Thm_D1Bound5_oneSmallCutoffRows_finiteN2FixedBound
-- name    : D1Bound5.oneSmallCutoffRows_finiteN2FixedBound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:47:55.533962+00:00
-- url     : https://prove2.me/theorems/17adbd8e-d2df-4b17-9819-196a3075fe74
-- title:
--   One Small Cutoff Rows finite N2Fixed Bound
-- statement:
--   Each of the57 actual cutoff triples has exact coefficient-square certificates for the manuscript's M2, computed from the proved N2 integer coefficient vectors.
-- source:
--   D1Bound5/OneSmallN2FixedArithmetic.lean, lines 436-500, SHA-256 164624a5c23628e859c312cd4e25138d33e47f04cca6c8177425d4c89d42a3cd. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallN2FixedArithmetic_Definitions

section
namespace D1Bound5
open QuadInt







set_option maxRecDepth 100000
set_option maxHeartbeats 0






































































































































































































































theorem _root_.D1Bound5.oneSmallCutoffRows_finiteN2FixedBound (r : OneSmallCutoffRow)
    (hr : r ∈ oneSmallCutoffRows) :
    ∃ w : Fin 3 → Fin 2 → Fin 3 → ℚ, FiniteN2FixedBound r w := by sorry

end D1Bound5
end
