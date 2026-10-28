-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared30_sieve_eq
-- name    : D1Bound5.PairLightPrepared30.sieve_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:19:43.598996+00:00
-- url     : https://prove2.me/theorems/1b16e422-6533-40c2-b916-e9770b2e8714
-- title:
--   Pair Light Prepared30 — sieve eq
-- statement:
--   Auxiliary result `PairLightPrepared30.sieve_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly30.lean, lines 10-11, SHA-256 d3e271a46210b697f08a25cf096f1dd3e031fd5faa932a54c831d00cc7dbd661. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightPrepared30.sieve_eq : sieve = smallPairSieve_1_1 := by sorry

















end D1Bound5.PairLightPrepared30
end
