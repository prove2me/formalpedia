-- Prove2me | Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentBool_eq_raw
-- name    : D1Bound5.pairLightSelectedFloorIndependentBool_eq_raw
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:07.973703+00:00
-- url     : https://prove2.me/theorems/b8afe451-548c-4a18-8797-3bea42080fbd
-- title:
--   Pair Light Selected Floor Independent Bool eq raw
-- statement:
--   Auxiliary result `pairLightSelectedFloorIndependentBool_eq_raw` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairLightArithmeticBridge.lean, lines 119-133, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51. Project: https://github.com/tomislav-math/d1-bound5-lean

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































theorem _root_.D1Bound5.pairLightSelectedFloorIndependentBool_eq_raw {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ)) :
    pairLightSelectedFloorIndependentBool tau nu sieve
      (cached.map pairLightCachedCoordinates) rows =
      pairRawSelectedFloorIndependentBool sieve cached rows := by sorry









end D1Bound5
end
