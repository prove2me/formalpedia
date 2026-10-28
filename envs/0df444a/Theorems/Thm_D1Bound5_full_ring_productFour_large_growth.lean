-- Prove2me | Theorems.Thm_D1Bound5_full_ring_productFour_large_growth
-- name    : D1Bound5.full_ring_productFour_large_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:45.886896+00:00
-- url     : https://prove2.me/theorems/1a451f28-9bc1-42f8-ae9b-4db306a36f1b
-- title:
--   Full ring product Four large growth
-- statement:
--   The A >= 3 part of the four-entry determinant growth lemma, for every imaginary quadratic FULL integer ring. The tail-growth assumption is the separately proved irregular-tail lemma, not a replacement for the result.
-- source:
--   D1Bound5/ProductFourLargeBranch.lean, lines 47-110, SHA-256 4851402ecfc8290d9255d8a258c4878b20354f6555e88cd106cf24ffdca061f8. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.Int.GCD
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5





end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.full_ring_productFour_large_growth
    {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (M : Matrix (Fin 4) (Fin 4) (𝓞 K))
    (hdiag : ∀ i, M i i = a i)
    (hsymm : ∀ i j, M i j = M j i)
    (hroot : ∀ i j, i ≠ j → (M i j)^2 = a i * a j + 1)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 3 ≤ ‖phi (a 0 : K)‖)
    (htail : 2 * ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖) :
    2 * ‖phi (a 0 : K)‖ * ‖phi (a 1 : K)‖ * ‖phi (a 2 : K)‖ <
      ‖phi (a 3 : K)‖ := by sorry

end D1Bound5
end
