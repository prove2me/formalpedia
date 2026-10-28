-- Prove2me | Theorems.Thm_D1Bound5_pairLightSelectedMaskRejectBool_eq_raw
-- name    : D1Bound5.pairLightSelectedMaskRejectBool_eq_raw
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:33.333334+00:00
-- url     : https://prove2.me/theorems/4244dee1-3f5f-4ed1-91d4-0c7504964ded
-- title:
--   Pair Light Selected Mask Reject Bool eq raw
-- statement:
--   Auxiliary result `pairLightSelectedMaskRejectBool_eq_raw` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairLightArithmeticBridge.lean, lines 77-87, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions

section
namespace D1Bound5























theorem _root_.D1Bound5.pairLightSelectedMaskRejectBool_eq_raw (tau nu : ℤ) (sieve : List (ℕ × ℕ))
    (xs ys : PairLightSignature) (i : ℕ) :
    pairLightSelectedMaskRejectBool tau nu sieve xs ys i =
      pairSelectedCachedMaskNatRejectBool tau nu sieve xs ys i := by sorry

















end D1Bound5
end
