-- Prove2me | Theorems.Thm_D1Bound5_pairRawSelectedFloorRowBool_eq
-- name    : D1Bound5.pairRawSelectedFloorRowBool_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:38.525992+00:00
-- url     : https://prove2.me/theorems/264b6412-915d-45e3-8af1-85a43386f83f
-- title:
--   Pair Raw Selected Floor Row Bool eq
-- statement:
--   Equality holds for arbitrary words, signatures, and floor lists, including malformed certificates; this is not merely one-way soundness.
-- source:
--   D1Bound5/PairRawSelectedFloorWitnesses.lean, lines 50-62, SHA-256 16663ee7ed18799dce07207a0b374d05787f04c1c37fca43ad73b4907ad0a013. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.pairRawSelectedFloorRowBool_eq {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (x : PairResidueVertex tau nu) (ys : List (PairResidueVertex tau nu))
    (code : ℕ) (ks : List ℕ) :
    pairRawSelectedFloorRowBool sieve x ys code ks =
      pairSelectedFloorRowBool sieve x ys code ks := by sorry











end D1Bound5
end
