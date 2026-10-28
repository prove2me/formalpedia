-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_productFour_large_growth
-- name    : D1Bound5.IsD1Tuple.productFour_large_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:52:54.652436+00:00
-- url     : https://prove2.me/theorems/9bff3d1a-bfce-42f8-90cb-423d8230fc89
-- title:
--   Is D1Tuple — product Four large growth
-- statement:
--   The A >= 3 branch of product-four stated for an actual ordered D(1) quadruple: no auxiliary root-matrix or tail-growth hypothesis remains.
-- source:
--   D1Bound5/TupleRootMatrixBridge.lean, lines 68-84, SHA-256 18bf68c70f7461d132ff1bb7a87d58364bb611e213e0471f018bd1b883568dd6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField
open Module

namespace D1Bound5












theorem _root_.D1Bound5.IsD1Tuple.productFour_large_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hA : 3 ≤ ‖phi (t 0 : K)‖) :
    2 * ‖phi (t 0 : K)‖ * ‖phi (t 1 : K)‖ *
      ‖phi (t 2 : K)‖ < ‖phi (t 3 : K)‖ := by sorry

end D1Bound5
end
