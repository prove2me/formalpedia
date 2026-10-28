-- Prove2me | Theorems.Thm_D1Bound5_pairRawSelectedFloorIndependentBool_eq
-- name    : D1Bound5.pairRawSelectedFloorIndependentBool_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:06.160102+00:00
-- url     : https://prove2.me/theorems/ab435b04-cbc8-4bd5-9f15-aa5bccc2de7a
-- title:
--   Pair Raw Selected Floor Independent Bool eq
-- statement:
--   Auxiliary result `pairRawSelectedFloorIndependentBool_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairRawSelectedFloorWitnesses.lean, lines 73-86, SHA-256 16663ee7ed18799dce07207a0b374d05787f04c1c37fca43ad73b4907ad0a013. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions
import Definitions.Def_D1Bound5_PairSelectedFloorWitnesses_Definitions

section
namespace D1Bound5











theorem _root_.D1Bound5.pairRawSelectedFloorIndependentBool_eq {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ)) :
    pairRawSelectedFloorIndependentBool sieve cached rows =
      pairSelectedFloorIndependentBool sieve cached rows := by sorry







end D1Bound5
end
