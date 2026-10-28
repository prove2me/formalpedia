-- Prove2me | Theorems.Thm_D1Bound5_productFive_bilinear_l2_le
-- name    : D1Bound5.productFive_bilinear_l2_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:38.314424+00:00
-- url     : https://prove2.me/theorems/145c1316-7799-423e-aeb1-9b4e0a733b43
-- title:
--   Product Five bilinear l2 le
-- statement:
--   Complex bilinear Cauchy--Schwarz, with the conjugate used only inside the Hilbert-space inner product.
-- source:
--   D1Bound5/ProductFiveSignedPrefixInverse.lean, lines 93-119, SHA-256 b442e4bc92f1e012f701af373bcc83cfa40c6dc48acdf69dbbcdc1ca68e89c60. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





end D1Bound5

open scoped InnerProductSpace

namespace D1Bound5


theorem _root_.D1Bound5.productFive_bilinear_l2_le (v w : Fin 4 → ℂ) :
    ‖v ⬝ᵥ w‖ ≤
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 4))‖ *
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ := by sorry





end D1Bound5
end
