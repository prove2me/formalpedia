-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_row_lift
-- name    : D1Bound5.bennettTwoClearedEntry_row_lift
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:36.800002+00:00
-- url     : https://prove2.me/theorems/0c70a398-e81e-4fe1-b8ba-20c10bb49c51
-- title:
--   Bennett Two Cleared Entry row lift
-- statement:
--   Every actual two-anchor row lifts to the original ring, with the exact column powers retained. Instantiating R with the full ring of integers gives the arithmetic integrality/divisibility bridge without unique factorization.
-- source:
--   D1Bound5/BennettTwoIntegralEntries.lean, lines 153-179, SHA-256 07d63d84699ae294fc3d395f046972fa36aa179a18de306e5f612beceaaf5f1b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralEntries_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]




























theorem _root_.D1Bound5.bennettTwoClearedEntry_row_lift
    {R : Type*} [CommRing R] (f : R →+* F) (a b c : R)
    (ha0 : f a ≠ 0) (hb0 : f b ≠ 0) (hab : f a ≠ f b)
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ q0 q1 q2 : R,
      f q0 = bennettTwoClearedEntry (f a) (f b) (f c) k i 0 ∧
      f (a ^ k * q1) = bennettTwoClearedEntry (f a) (f b) (f c) k i 1 ∧
      f (b ^ k * q2) = bennettTwoClearedEntry (f a) (f b) (f c) k i 2 := by sorry

end D1Bound5
end
