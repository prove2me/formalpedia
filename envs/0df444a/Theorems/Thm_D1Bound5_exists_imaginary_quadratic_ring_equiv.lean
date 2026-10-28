-- Prove2me | Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
-- name    : D1Bound5.exists_imaginary_quadratic_ring_equiv
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:51:05.623351+00:00
-- url     : https://prove2.me/theorems/a4073106-b4ab-4834-b6a5-67317da85231
-- title:
--   Exists imaginary quadratic ring equiv
-- statement:
--   Every imaginary quadratic field has full integer-ring coordinates of trace zero or one and positive discriminant. There is no suborder hypothesis.
-- source:
--   D1Bound5/FullRingBridge.lean, lines 37-45, SHA-256 dc7878b5987408dc5ad74248ad83af5608a906791f27df468ed3d05ac252ac2f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField ComplexConjugate
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]




theorem _root_.D1Bound5.exists_imaginary_quadratic_ring_equiv (hK : finrank ℚ K = 2) :
    ∃ tau nu : ℤ, (tau = 0 ∨ tau = 1) ∧ 0 < QuadInt.discriminant tau nu ∧
      Nonempty (QuadInt tau nu ≃+* 𝓞 K) := by sorry







end D1Bound5
end
