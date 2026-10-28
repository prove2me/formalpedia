-- Prove2me | Theorems.Thm_D1Bound5_pairLightIndexedRootWitnessCheckedBool_eq
-- name    : D1Bound5.pairLightIndexedRootWitnessCheckedBool_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:53.114611+00:00
-- url     : https://prove2.me/theorems/1ca3a0e9-b341-4db2-9c30-791b525b4b9a
-- title:
--   Pair Light Indexed Root Witness Checked Bool eq
-- statement:
--   Auxiliary result `pairLightIndexedRootWitnessCheckedBool_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairLightClosureBridge.lean, lines 54-64, SHA-256 0da6268742f73a449f0c5571cfb1ac1e208c0ee42ca0b3c987a294921bc357aa. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairLightClosureBridge_Definitions
import Definitions.Def_D1Bound5_PairLightClosure_Definitions

section
namespace D1Bound5











theorem _root_.D1Bound5.pairLightIndexedRootWitnessCheckedBool_eq {tau nu : ℤ}
    (a b r0 : QuadInt tau nu) (bound : ℤ) (vertices : List (QuadInt tau nu))
    (w : PairRootWitness tau nu) (destinations : Option Nat × Option Nat) :
    pairLightIndexedRootWitnessCheckedBool tau nu
      (pairLightCoordinates a) (pairLightCoordinates b) (pairLightCoordinates r0) bound
      (vertices.map pairLightCoordinates) (pairLightRootWitnessCoordinates w) destinations =
      pairIndexedRootWitnessCheckedBool a b r0 bound vertices w destinations := by sorry



end D1Bound5
end
