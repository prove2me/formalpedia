-- Prove2me | Theorems.Thm_D1Bound5_pell_norm_two_is_convergent
-- name    : D1Bound5.pell_norm_two_is_convergent
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:31.530362+00:00
-- url     : https://prove2.me/theorems/f9864cb2-0174-4bf4-87ae-d290cc2c1a59
-- title:
--   Pell norm two is convergent
-- statement:
--   The norm-two equation gives the strict Legendre approximation, including the reduced denominator. This is an actual Pell theorem, not an assumed continued-fraction enumeration.
-- source:
--   D1Bound5/PellConvergentCompleteness.lean, lines 119-154, SHA-256 c43074daa228222fbe1ca798070304a8be11d05710c382ec9a9e73d7799c8266. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

section
namespace D1Bound5




















theorem _root_.D1Bound5.pell_norm_two_is_convergent {d x y : ℤ} (hd : 7 ≤ d)
    (hx : 0 < x) (hy : 0 < y) (heq : x^2-d*y^2=2) :
    ∃ n, (x/y : ℚ) = (Real.sqrt (d : ℝ)).convergent n := by sorry



end D1Bound5
end
