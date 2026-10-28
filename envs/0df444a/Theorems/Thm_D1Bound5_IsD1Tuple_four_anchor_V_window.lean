-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_four_anchor_V_window
-- name    : D1Bound5.IsD1Tuple.four_anchor_V_window
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:31.219986+00:00
-- url     : https://prove2.me/theorems/d813055e-51d4-4f50-8403-e5ffafccc235
-- title:
--   Is D1Tuple — four anchor V window
-- statement:
--   The V-window exclusion for an actual ordered D(1) sextuple. Nonvanishing, integrality, root signs and root-size estimates are all derived inside the theorem.
-- source:
--   D1Bound5/FourAnchorVWindow.lean, lines 41-107, SHA-256 745b5229447b46b23cd565d6e05245ce882a6a77d258e5d7beee2c8be63afe71. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Definitions.Def_D1Bound5_IsD1Tuple

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.four_anchor_V_window
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hP : 1000 ≤ ‖phi (a 4 : K)‖)
    (hTP : 4*‖phi (a 3 : K)‖ ≤ ‖phi (a 4 : K)‖)
    (hQ : 4*‖phi (a 4 : K)‖ ≤ ‖phi (a 5 : K)‖)
    (hsize : 32*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖/
      ‖phi (a 0 : K)‖^3 ≤ ‖phi (a 4 : K)‖^2) :
    ‖phi (a 5 : K)‖ < 101*‖phi (a 1 : K)‖^2*‖phi (a 3 : K)‖^4/
        ‖phi (a 4 : K)‖ ∨
      (2/5 : ℝ)*‖phi (a 0 : K)‖^2*‖phi (a 4 : K)‖^5/
        ‖phi (a 3 : K)‖^2 < ‖phi (a 5 : K)‖ := by sorry

end D1Bound5
end
