-- Prove2me | Theorems.Thm_D1Bound5_full_ring_scaledRootMatrix_det_norm_lower
-- name    : D1Bound5.full_ring_scaledRootMatrix_det_norm_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:04.631847+00:00
-- url     : https://prove2.me/theorems/de6365f3-297d-472b-8bce-3cdfab4a47f1
-- title:
--   Full ring scaled Root Matrix det norm lower
-- statement:
--   For every imaginary quadratic FULL integer ring, the root-square relations give the arithmetic determinant lower bound in even dimension.
-- source:
--   D1Bound5/RootDeterminantLower.lean, lines 38-54, SHA-256 3d02f2749dfbdd091a145b68010d8c3853da3cc250556f78c0e8042ffaf6746c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions

section
open scoped NumberField BigOperators
open Module

namespace D1Bound5






theorem _root_.D1Bound5.full_ring_scaledRootMatrix_det_norm_lower
    {K n : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] [Fintype n] [DecidableEq n]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (hn : Even (Fintype.card n))
    (a : n → 𝓞 K) (M : Matrix n n (𝓞 K))
    (hd : ∀ i, M i i = a i)
    (hs : ∀ i j, i ≠ j → (M i j)^2 = a i*a j+1)
    (u : n → ℂ) (hu : ∀ i, (u i)^2 = phi (a i : K)) :
    (∏ i, ‖phi (a i : K)‖) ≤
      ‖(scaledRootMatrix u
        (M.map (phi.comp (algebraMap (𝓞 K) K)))).det‖ := by sorry

end D1Bound5
end
