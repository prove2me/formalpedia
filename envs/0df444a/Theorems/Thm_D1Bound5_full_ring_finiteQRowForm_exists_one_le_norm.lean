-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteQRowForm_exists_one_le_norm
-- name    : D1Bound5.full_ring_finiteQRowForm_exists_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:11.864735+00:00
-- url     : https://prove2.me/theorems/670f7133-e347-48cf-a3e8-75e0188bca7a
-- title:
--   Full ring finite QRow Form exists one le norm
-- statement:
--   Full-ring arithmetic lower bound for one actual finite Q row. The selected row is an integer polynomial combination of the supplied roots, and its nonvanishing comes from the explicit determinant above.
-- source:
--   D1Bound5/FiniteQIntegralRows.lean, lines 73-111, SHA-256 13dbc71d3f13cc35a26b1a62808a9ec3ba2232668209833fc8f21e0bdba9f6ad. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {R S : Type*} [CommRing R] [CommRing S]
















theorem _root_.D1Bound5.full_ring_finiteQRowForm_exists_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b s t c z rA rB rS rT : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hat : a ≠ t)
    (hbs : b ≠ s) (hbt : b ≠ t) (hst : s ≠ t) (hz : z ≠ 0) :
    ∃ i : Fin 5, 1 ≤ ‖finiteQRowForm
      (phi (a : K)) (phi (b : K)) (phi (s : K)) (phi (t : K)) (phi (c : K))
      (phi (z : K)) (phi (rA : K)) (phi (rB : K)) (phi (rS : K)) (phi (rT : K)) i‖ := by sorry

end D1Bound5
end
