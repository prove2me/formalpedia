-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_direct_four_integer_inequality
-- name    : D1Bound5.IsD1Tuple.direct_four_integer_inequality
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:56.91812+00:00
-- url     : https://prove2.me/theorems/1fa34e10-8c25-4d7b-8980-8d2d42200a46
-- title:
--   Is D1Tuple — direct four integer inequality
-- statement:
--   Beyond the proved zero-form upper window, an actual sextuple supplies the direct-four integral inequality and terminal norm bounds.
-- source:
--   D1Bound5/FullRingDirectFour.lean, lines 36-110, SHA-256 26f682adf7b364982556911f0c653055c60090d901726c7071aa654e23955b54. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Definitions.Def_D1Bound5_IsD1Tuple

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5






theorem _root_.D1Bound5.IsD1Tuple.direct_four_integer_inequality
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hC : 1000 ≤ ‖phi (a 4 : K)‖)
    (hD : 1000*‖phi (a 4 : K)‖ ≤ ‖phi (a 5 : K)‖)
    (hzeroExcluded : 17*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*
      ‖phi (a 3 : K)‖*‖phi (a 4 : K)‖^3 ≤ ‖phi (a 5 : K)‖) :
    ∃ Z : ℝ, 0 < Z ∧ ‖phi (a 4 : K)‖/2 < Z ∧
      Z^2 ≤ 2*‖phi (a 4 : K)‖*‖phi (a 5 : K)‖ ∧
      1 < 13*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^2*‖phi (a 3 : K)‖^3/Z+
        49*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^2*Z/
          (50*‖phi (a 0 : K)‖*‖phi (a 4 : K)‖^4) := by sorry

end D1Bound5
end
