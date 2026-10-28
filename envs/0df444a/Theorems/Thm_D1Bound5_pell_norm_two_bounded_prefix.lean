-- Prove2me | Theorems.Thm_D1Bound5_pell_norm_two_bounded_prefix
-- name    : D1Bound5.pell_norm_two_bounded_prefix
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:41.247738+00:00
-- url     : https://prove2.me/theorems/b930085c-4885-4fd9-bb25-8d277a3825cf
-- title:
--   Pell norm two bounded prefix
-- statement:
--   A checked stopping numerator makes the finite prefix complete for every positive norm-two solution with bounded numerator. No solution list is an input hypothesis.
-- source:
--   D1Bound5/PellConvergentCompleteness.lean, lines 156-185, SHA-256 c43074daa228222fbe1ca798070304a8be11d05710c382ec9a9e73d7799c8266. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions

section
namespace D1Bound5






















theorem _root_.D1Bound5.pell_norm_two_bounded_prefix {d x y X : ℤ} {N : ℕ}
    (hd : 7 ≤ d) (hns : ¬IsSquare d) (hx : 0 < x) (hy : 0 < y)
    (heq : x^2-d*y^2=2) (hX : x ≤ X)
    (hstop : X < (pellConvergentPair (Real.sqrt (d : ℝ)) N).1) :
    ∃ n < N, pellConvergentPair (Real.sqrt (d : ℝ)) n = (x,y) := by sorry

end D1Bound5
end
