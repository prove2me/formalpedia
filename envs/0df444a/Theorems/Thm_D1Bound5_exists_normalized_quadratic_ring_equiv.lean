-- Prove2me | Theorems.Thm_D1Bound5_exists_normalized_quadratic_ring_equiv
-- name    : D1Bound5.exists_normalized_quadratic_ring_equiv
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:52:15.132996+00:00
-- url     : https://prove2.me/theorems/bdb2de2c-039e-4a6e-b7c3-7512903f137d
-- title:
--   Exists normalized quadratic ring equiv
-- statement:
--   Every quadratic number ring has normalized integral coordinates with trace zero or one. No maximal-order or discriminant condition is assumed.
-- source:
--   D1Bound5/FullRingBasis.lean, lines 116-123, SHA-256 7a7a55f350ab7d5224275914efa11b126ec34a9ae9cc9e505c2669503411924c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K]









theorem _root_.D1Bound5.exists_normalized_quadratic_ring_equiv (hK : finrank ℚ K = 2) :
    ∃ tau nu : ℤ, (tau = 0 ∨ tau = 1) ∧ Nonempty (QuadInt tau nu ≃+* 𝓞 K) := by sorry

end D1Bound5
end
