-- Prove2me | Theorems.Thm_D1Bound5_quadInt_mul_eq_zero
-- name    : D1Bound5.quadInt_mul_eq_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:29.126984+00:00
-- url     : https://prove2.me/theorems/5c9624bb-d6b4-4eff-a9c4-1ed3b4ad3ee2
-- title:
--   Quad Int mul eq zero
-- statement:
--   Positive-definite quadratic coordinates have no zero divisors.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 89-97, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt
















theorem _root_.D1Bound5.quadInt_mul_eq_zero {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    {x y : QuadInt tau nu} (h : x*y = 0) : x = 0 ∨ y = 0 := by sorry



















end D1Bound5
end
