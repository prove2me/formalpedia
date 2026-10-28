-- Prove2me | Theorems.Thm_D1Bound5_finiteN3BsCutoffWeights_21_valid
-- name    : D1Bound5.finiteN3BsCutoffWeights_21_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:37.653484+00:00
-- url     : https://prove2.me/theorems/d49122a0-faa3-460b-907f-93bab2f1efa6
-- title:
--   N₃ coefficient bound for finiteN3BsCutoffWeights_21
-- statement:
--   The rational weights `finiteN3BsCutoffWeights_21` give an evaluated N₃ coefficient certificate for the anchors `oneSmallCutoffRow_21.triple.anchorB` and `oneSmallCutoffRow_21.triple.anchorS`. All weights are nonnegative, every coefficient norm satisfies its prescribed weighted bound, and each row’s total weight, multiplied by 101/100, is strictly less than `oneSmallCutoffRow_21.Mbs`. The coefficients incorporate the integer row divisor.
-- source:
--   D1Bound5/OneSmallN3BsFixedArithmetic.lean, lines 203-207, SHA-256 4f43bff1dfec8db0799fdf167ba9ac59a3ba3fbd4a2f46b730480076a61b255b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteN3FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallN3BsFixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/- Exact evaluated N3 coefficient certificates on the bs anchors. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0























































































theorem _root_.D1Bound5.finiteN3BsCutoffWeights_21_valid :
    FiniteN3FixedBound oneSmallCutoffRow_21.triple.anchorB
      oneSmallCutoffRow_21.triple.anchorS oneSmallCutoffRow_21.Mbs
      finiteN3BsCutoffWeights_21 := by sorry















































































































































end D1Bound5
end
