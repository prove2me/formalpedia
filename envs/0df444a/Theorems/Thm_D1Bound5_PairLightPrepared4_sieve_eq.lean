-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared4_sieve_eq
-- name    : D1Bound5.PairLightPrepared4.sieve_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:12.006632+00:00
-- url     : https://prove2.me/theorems/5308054b-3672-41e2-8e60-36df1305f076
-- title:
--   Pair Light Prepared4 — sieve eq
-- statement:
--   Auxiliary result `PairLightPrepared4.sieve_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly4.lean, lines 10-11, SHA-256 a33d4d40649da2331bd8a9202b6f96f06e58f1b224932a9a23787556c880875f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared4.sieve_eq : sieve = smallPairSieve_0_1 := by sorry

















end D1Bound5.PairLightPrepared4
end
