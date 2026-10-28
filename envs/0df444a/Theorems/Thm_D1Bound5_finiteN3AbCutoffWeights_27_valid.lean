-- Prove2me | Theorems.Thm_D1Bound5_finiteN3AbCutoffWeights_27_valid
-- name    : D1Bound5.finiteN3AbCutoffWeights_27_valid
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:33:51.007707+00:00
-- url     : https://prove2.me/theorems/b81719a2-58af-473e-98b4-13c5ad048443
-- title:
--   N₃ coefficient bound for finiteN3AbCutoffWeights_27
-- statement:
--   The rational weights `finiteN3AbCutoffWeights_27` give an evaluated N₃ coefficient certificate for the anchors `oneSmallCutoffRow_27.triple.anchorA` and `oneSmallCutoffRow_27.triple.anchorB`. All weights are nonnegative, every coefficient norm satisfies its prescribed weighted bound, and each row’s total weight, multiplied by 101/100, is strictly less than `oneSmallCutoffRow_27.Mn`. The coefficients incorporate the integer row divisor.
-- source:
--   D1Bound5/OneSmallN3AbFixedArithmetic.lean, lines 257-261, SHA-256 c4e17b5c41fbd6a8ab71c64b13d026787c2d0b699f64a6314bd1bca495ab8385. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_OneSmallN3AbFixedArithmetic_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/- Exact evaluated N3 coefficient certificates on the ab anchors. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0















































































































theorem _root_.D1Bound5.finiteN3AbCutoffWeights_27_valid :
    FiniteN3FixedBound oneSmallCutoffRow_27.triple.anchorA
      oneSmallCutoffRow_27.triple.anchorB oneSmallCutoffRow_27.Mn
      finiteN3AbCutoffWeights_27 := by sorry























































































































end D1Bound5
end
