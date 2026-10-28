-- Prove2me | Theorems.Thm_D1Bound5_exists_integral_generator
-- name    : D1Bound5.exists_integral_generator
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:11.636137+00:00
-- url     : https://prove2.me/theorems/092a5ffb-7cd1-4ac2-b1fa-d600eed39d83
-- title:
--   Exists integral generator
-- statement:
--   A quadratic number ring has an integral basis of the form one, omega. Bijectivity means that every algebraic integer, not just an order, has a unique pair of integer coordinates in this basis.
-- source:
--   D1Bound5/FullRingBasis.lean, lines 42-95, SHA-256 7a7a55f350ab7d5224275914efa11b126ec34a9ae9cc9e505c2669503411924c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K]





theorem _root_.D1Bound5.exists_integral_generator (hK : finrank ℚ K = 2) :
    ∃ w : 𝓞 K, Function.Bijective (fun p : ℤ × ℤ => (p.1 : 𝓞 K) + (p.2 : 𝓞 K)*w) := by sorry





end D1Bound5
end
