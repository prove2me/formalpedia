-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedEntry_one_integral_divisible
-- name    : D1Bound5.bennettTwoClearedEntry_one_integral_divisible
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:36:58.134565+00:00
-- url     : https://prove2.me/theorems/8e7abfaf-26ed-4ec1-8543-43e68057b38b
-- title:
--   Bennett Two Cleared Entry one integral divisible
-- statement:
--   The entire column-one entry is divisible by a^k in the original subring.
-- source:
--   D1Bound5/BennettTwoIntegralEntries.lean, lines 94-114, SHA-256 07d63d84699ae294fc3d395f046972fa36aa179a18de306e5f612beceaaf5f1b. Project: https://github.com/tomislav-math/d1-bound5-lean

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






















theorem _root_.D1Bound5.bennettTwoClearedEntry_one_integral_divisible (S : Subring F)
    (a b c : F) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hb0 : b ≠ 0) (hab : a ≠ b) (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ∃ q ∈ S, bennettTwoClearedEntry a b c k i 1 = a ^ k * q := by sorry







end D1Bound5
end
