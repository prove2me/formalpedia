-- Prove2me | Theorems.Thm_D1Bound5_pellConvergentPair_div
-- name    : D1Bound5.pellConvergentPair_div
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:55.879022+00:00
-- url     : https://prove2.me/theorems/3ed27dfb-99dd-4b1c-9e3f-54ef9d1478b2
-- title:
--   Pell Convergent Pair div
-- statement:
--   Auxiliary result `pellConvergentPair_div` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PellConvergentCompleteness.lean, lines 54-70, SHA-256 c43074daa228222fbe1ca798070304a8be11d05710c382ec9a9e73d7799c8266. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions

section
namespace D1Bound5











theorem _root_.D1Bound5.pellConvergentPair_div {x : ℝ} (hx : Irrational x) (hx1 : 1 < x)
    (n : ℕ) :
    ((pellConvergentPair x n).1 : ℚ) / (pellConvergentPair x n).2 = x.convergent n := by sorry











end D1Bound5
end
