-- Prove2me | Theorems.Thm_D1Bound5_finiteA5CutoffWeights_15_valid
-- name    : D1Bound5.finiteA5CutoffWeights_15_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:34:15.390227+00:00
-- url     : https://prove2.me/theorems/2e50872e-3452-40dd-aaf9-6ada4910b1cb
-- title:
--   A₅ coefficient bound for finiteA5CutoffWeights_15
-- statement:
--   The rational weights `finiteA5CutoffWeights_15` give an evaluated A₅ coefficient certificate for the anchors `oneSmallCutoffRow_15.triple.anchorA` and `oneSmallCutoffRow_15.triple.anchorB`. All weights are nonnegative, every coefficient norm satisfies its prescribed weighted bound, and each row’s total weight, multiplied by 101/100, is strictly less than `oneSmallCutoffRow_15.M5`. The coefficients incorporate the integer row divisor.
-- source:
--   D1Bound5/OneSmallA5FixedArithmetic.lean, lines 151-155, SHA-256 b57f534901e12ebb1bb197f17c1f190ebae73c1a8434baaf95362070b147d9b3. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteA5FixedHeight_Definitions
import Definitions.Def_D1Bound5_OneSmallA5FixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/- Each exact square certificate evaluates the actual divided A5 root
coefficient in the quadratic integer ring before taking its field norm.
It then checks the printed M5 with a strict rational row-sum comparison. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0































































theorem _root_.D1Bound5.finiteA5CutoffWeights_15_valid :
    FiniteA5FixedBound oneSmallCutoffRow_15.triple.anchorA
      oneSmallCutoffRow_15.triple.anchorB oneSmallCutoffRow_15.M5
      finiteA5CutoffWeights_15 := by sorry







































































































































































end D1Bound5
end
