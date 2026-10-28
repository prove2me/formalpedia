-- Prove2me | Theorems.Thm_D1Bound5_pairLightIndexedCandidateCoveredBool_eq
-- name    : D1Bound5.pairLightIndexedCandidateCoveredBool_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:49.730829+00:00
-- url     : https://prove2.me/theorems/0da737df-175a-470a-8e47-cd227abbb196
-- title:
--   Pair Light Indexed Candidate Covered Bool eq
-- statement:
--   The identity holds for every list and supplied index, including malformed indices and the strict outside-bound case. No certificate validity is assumed.
-- source:
--   D1Bound5/PairLightClosureBridge.lean, lines 34-52, SHA-256 0da6268742f73a449f0c5571cfb1ac1e208c0ee42ca0b3c987a294921bc357aa. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.pairLightIndexedCandidateCoveredBool_eq {tau nu : ℤ} (bound : ℤ)
    (vertices : List (QuadInt tau nu)) (w : QuadInt tau nu)
    (destination : Option Nat) :
    pairLightIndexedCandidateCoveredBool tau nu bound
      (vertices.map pairLightCoordinates) (pairLightCoordinates w) destination =
      pairIndexedCandidateCoveredBool bound vertices w destination := by sorry





end D1Bound5
end
