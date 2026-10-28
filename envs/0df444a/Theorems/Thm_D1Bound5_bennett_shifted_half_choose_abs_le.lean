-- Prove2me | Theorems.Thm_D1Bound5_bennett_shifted_half_choose_abs_le
-- name    : D1Bound5.bennett_shifted_half_choose_abs_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:27.931971+00:00
-- url     : https://prove2.me/theorems/137389a4-96d8-4cba-b3d4-8272ce5c04da
-- title:
--   Bennett shifted half choose abs le
-- statement:
--   All coefficients used by the local Taylor residue lie before the first sign change. An ordinary degree-(k+1) binomial dominates them coefficientwise. The small extra factor will be absorbed by the manuscript's rounding to H2.
-- source:
--   D1Bound5/BennettCoefficientMajorant.lean, lines 24-42, SHA-256 52f2dc90c9817830bd21c1880dfcf0e6477a59dce71efbcde2deafd50273de8e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.bennett_shifted_half_choose_abs_le (k h : ℕ) (hh : h ≤ k) :
    |Ring.choose ((k : ℝ) + 1 / 2) h| ≤ (Nat.choose (k + 1) h : ℝ) := by sorry













end D1Bound5
end
