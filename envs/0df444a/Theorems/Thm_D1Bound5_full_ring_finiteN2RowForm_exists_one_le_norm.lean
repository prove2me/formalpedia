-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteN2RowForm_exists_one_le_norm
-- name    : D1Bound5.full_ring_finiteN2RowForm_exists_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:09:42.459047+00:00
-- url     : https://prove2.me/theorems/55ab5b49-8b83-40e2-bbb6-c0930327ead3
-- title:
--   Full ring finite N2Row Form exists one le norm
-- statement:
--   One actual N2 integer row has modulus at least one. Both integrality and nonvanishing are obtained from the displayed polynomial construction.
-- source:
--   D1Bound5/FiniteN2IntegralRows.lean, lines 61-91, SHA-256 24e7bcc1d136549034d85c5aaaf506ddde891a0489583b3f2c16180cc599e2b1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2IntegralRows_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]
















theorem _root_.D1Bound5.full_ring_finiteN2RowForm_exists_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (x y c z sX sY : 𝓞 K) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, 1 ≤ ‖finiteN2RowForm (phi (x : K)) (phi (y : K))
      (phi (c : K)) (phi (z : K)) (phi (sX : K)) (phi (sY : K)) i‖ := by sorry

end D1Bound5
end
