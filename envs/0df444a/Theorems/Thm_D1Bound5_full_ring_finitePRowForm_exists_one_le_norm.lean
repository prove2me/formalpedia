-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finitePRowForm_exists_one_le_norm
-- name    : D1Bound5.full_ring_finitePRowForm_exists_one_le_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:33.344935+00:00
-- url     : https://prove2.me/theorems/b63a97cf-cd4b-42f7-ab8c-fb63e567ffea
-- title:
--   Full ring finite PRow Form exists one le norm
-- statement:
--   A genuine full-ring integral row has norm at least one. Both the nonsingularity and the integrality of this constructed P matrix are proved here; they are not supplied as separate approximation certificates.
-- source:
--   D1Bound5/FinitePIntegralRows.lean, lines 140-187, SHA-256 f4ae4543e8d296d5524652a8ec1de382e8c69fd4002555ade9ad3f247eeee37c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePIntegralRows_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5






















theorem _root_.D1Bound5.full_ring_finitePRowForm_exists_one_le_norm
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b s c z rA rB rS : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) (hz : z ≠ 0)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hBS : ‖phi (b : K)‖ ≤ ‖phi (s : K)‖)
    (hC : 200*‖phi (s : K)‖ ≤ ‖phi (c : K)‖) :
    ∃ i : Fin 4, 1 ≤ ‖finitePRowForm (phi (a : K)) (phi (b : K)) (phi (s : K))
      (phi (c : K)) (phi (z : K)) (phi (rA : K)) (phi (rB : K)) (phi (rS : K)) i‖ := by sorry

end D1Bound5
end
