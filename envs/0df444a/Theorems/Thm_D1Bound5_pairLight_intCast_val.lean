-- Prove2me | Theorems.Thm_D1Bound5_pairLight_intCast_val
-- name    : D1Bound5.pairLight_intCast_val
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:50.805985+00:00
-- url     : https://prove2.me/theorems/18546677-fbcb-4d85-bcf9-9d11e3a50650
-- title:
--   Pair Light int Cast val
-- statement:
--   This is the pinned integer-cast residue identity, including negative z and modulus one. The modulus k+1 supplies the required nonzero instance.
-- source:
--   D1Bound5/PairLightArithmeticBridge.lean, lines 37-42, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
namespace D1Bound5












theorem _root_.D1Bound5.pairLight_intCast_val (k : ℕ) (z : ℤ) :
    (z : ZMod (k + 1)).val = (z % Int.ofNat (k + 1)).toNat := by sorry





























end D1Bound5
end
