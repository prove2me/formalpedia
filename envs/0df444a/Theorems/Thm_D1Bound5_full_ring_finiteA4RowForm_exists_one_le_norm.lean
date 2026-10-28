-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteA4RowForm_exists_one_le_norm
-- name    : D1Bound5.full_ring_finiteA4RowForm_exists_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:35:13.569247+00:00
-- url     : https://prove2.me/theorems/4219bf6a-3297-47d7-8d86-c0b4f5a05049
-- title:
--   Full ring finite A4Row Form exists one le norm
-- statement:
--   One actual A4 integer row has modulus at least one. Both integrality and nonvanishing are obtained from the displayed polynomial construction.
-- source:
--   D1Bound5/FiniteA4IntegralRows.lean, lines 61-96, SHA-256 b56979ac7f4b1c57a6032fbeb1344d28af0ac543b385ae16ed83d797b116c686. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_FiniteA4IntegralRows_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]
















theorem _root_.D1Bound5.full_ring_finiteA4RowForm_exists_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (x y c z sX sY : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (hxy : x ≠ y) (hz : z ≠ 0) :
    ∃ i : Fin 3, 1 ≤ ‖finiteA4RowForm (phi (x : K)) (phi (y : K))
      (phi (c : K)) (phi (z : K)) (phi (sX : K)) (phi (sY : K)) i‖ := by sorry

end D1Bound5
end
