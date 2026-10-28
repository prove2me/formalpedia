-- Prove2me | Theorems.Thm_D1Bound5_exists_full_integer_coordinates
-- name    : D1Bound5.exists_full_integer_coordinates
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:21:44.673597+00:00
-- url     : https://prove2.me/theorems/8015381a-0ea8-4278-8990-bfdeba7c9a12
-- title:
--   Exists full integer coordinates
-- statement:
--   The two full integer-ring models used in all finite computations. Every imaginary quadratic field is covered, with positive squarefree d and the half-integral model exactly when d is 3 modulo 4.
-- source:
--   D1Bound5/FullRingClassification.lean, lines 9-29, SHA-256 e53f31704f6ab515c54419ab5c745dab013cec5002a43430a644fe0477662aea. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
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
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.exists_full_integer_coordinates {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    ∃ d : ℤ, 0 < d ∧ Squarefree d ∧
      ((d % 4 = 3 ∧ Nonempty (QuadInt 1 ((d+1)/4) ≃+* 𝓞 K)) ∨
       (d % 4 ≠ 3 ∧ Nonempty (QuadInt 0 d ≃+* 𝓞 K))) := by sorry

end D1Bound5
end
