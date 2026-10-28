-- Prove2me | Theorems.Thm_D1Bound5_full_ring_productFour_mixed_growth
-- name    : D1Bound5.full_ring_productFour_mixed_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:43:37.688188+00:00
-- url     : https://prove2.me/theorems/b4788713-e275-4b39-acf2-cabca27134fd
-- title:
--   Full ring product Four mixed growth
-- statement:
--   The mixed A >= 1, B >= 3 growth estimate in every imaginary quadratic full integer ring. The original-ring square roots and sign choices are constructed without excluding zero squares or equal complex moduli.
-- source:
--   D1Bound5/MixedProductFourGrowth.lean, lines 104-218, SHA-256 6405700c83d4efaa313716abc06975c43c8dd7320d44c6d848be130386d5f504. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5














theorem _root_.D1Bound5.full_ring_productFour_mixed_growth
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (M : Matrix (Fin 4) (Fin 4) (𝓞 K))
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 1 ≤ ‖phi (a 0 : K)‖)
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (htail : 2 * ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ <
      ‖phi (a 3 : K)‖) :
    (3/2 : ℝ)*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*
      ‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖ := by sorry



end D1Bound5
end
