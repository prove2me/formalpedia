-- Prove2me | Theorems.Thm_D1Bound5_scaledRootMatrix_det_norm_lower
-- name    : D1Bound5.scaledRootMatrix_det_norm_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:43.067991+00:00
-- url     : https://prove2.me/theorems/3424a3ef-a489-42ff-8020-6ad03519221b
-- title:
--   Scaled Root Matrix det norm lower
-- statement:
--   The determinant bound needs only a lower bound for the unscaled integral determinant; no nonvanishing hypothesis on the coordinates.
-- source:
--   D1Bound5/RootDeterminantLower.lean, lines 26-36, SHA-256 3d02f2749dfbdd091a145b68010d8c3853da3cc250556f78c0e8042ffaf6746c. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.scaledRootMatrix_det_norm_lower
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (f : R →+* ℂ) (a : n → R) (u : n → ℂ)
    (M : Matrix n n R) (hu : ∀ i, (u i)^2 = f (a i))
    (hdet : 1 ≤ ‖f M.det‖) :
    (∏ i, ‖f (a i)‖) ≤ ‖(scaledRootMatrix u (M.map f)).det‖ := by sorry



end D1Bound5
end
