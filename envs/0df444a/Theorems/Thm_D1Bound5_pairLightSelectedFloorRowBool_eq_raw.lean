-- Prove2me | Theorems.Thm_D1Bound5_pairLightSelectedFloorRowBool_eq_raw
-- name    : D1Bound5.pairLightSelectedFloorRowBool_eq_raw
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:56.810307+00:00
-- url     : https://prove2.me/theorems/03266a0c-1353-4307-8881-d5c215308adb
-- title:
--   Pair Light Selected Floor Row Bool eq raw
-- statement:
--   Every tail position, invalid tag, duplicate, guard branch and floor-list case has exactly the old result. There is no data-validity premise.
-- source:
--   D1Bound5/PairLightArithmeticBridge.lean, lines 100-117, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions

section
namespace D1Bound5






























theorem _root_.D1Bound5.pairLightSelectedFloorRowBool_eq_raw {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (x : PairResidueVertex tau nu)
    (ys : List (PairResidueVertex tau nu)) (code : ℕ) (ks : List ℕ) :
    pairLightSelectedFloorRowBool tau nu sieve (pairLightCachedCoordinates x)
      (ys.map pairLightCachedCoordinates) code ks =
      pairRawSelectedFloorRowBool sieve x ys code ks := by sorry











end D1Bound5
end
