-- Prove2me | Theorems.Thm_D1Bound5_productFive_p_div_sq_norm_lt
-- name    : D1Bound5.productFive_p_div_sq_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:27.520259+00:00
-- url     : https://prove2.me/theorems/f89d9415-eff1-4fb6-a726-e1cd57488655
-- title:
--   Product Five p div sq norm lt
-- statement:
--   If the last modulus is at least 54, the normalized p-form is smaller than the exact rational threshold used in the determinant identity.
-- source:
--   D1Bound5/ProductFiveNormalizedQuadratic.lean, lines 50-63, SHA-256 f9e9847eb9518578e87809242291d3fb011ca50556f7c98e56d8bd121a0e2e9d. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.productFive_p_div_sq_norm_lt
    (p d : ℂ) (hp : ‖p‖ < 1) (hd : 54 ≤ ‖d‖) :
    ‖p/d^2‖ < (1/2916 : ℝ) := by sorry

end D1Bound5
end
