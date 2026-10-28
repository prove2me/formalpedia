-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared3_sieve_eq
-- name    : D1Bound5.PairLightPrepared3.sieve_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:41:34.718772+00:00
-- url     : https://prove2.me/theorems/ad727f93-620f-4f82-9595-fe5f6c97a99c
-- title:
--   Pair Light Prepared3 — sieve eq
-- statement:
--   Auxiliary result `PairLightPrepared3.sieve_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly3.lean, lines 10-11, SHA-256 56edac3dc1067d6b0f3c0222e535e97bb79b045082fc27258c676fd28249c84d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5.PairLightPrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared3.sieve_eq : sieve = smallPairSieve_0_1 := by sorry

















end D1Bound5.PairLightPrepared3
end
