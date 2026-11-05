-- Prove2me | Theorems.Thm_AnalyticEnclosures_expPoly_cast
-- name    : AnalyticEnclosures.expPoly_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/0cdc805d-f334-4e77-9005-801aa12deaa5
-- title:
--   AnalyticEnclosures: Exp Poly cast
-- statement:
--   Rational Taylor certificates imply inequalities for the actual real logarithm and exponential. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/AnalyticEnclosures.lean#L20-L22). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/AnalyticEnclosures.lean#L20-L22 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AnalyticEnclosures
set_option autoImplicit true
open AnalyticEnclosures
open scoped BigOperators

theorem AnalyticEnclosures.expPoly_cast (x : ℚ) (n : ℕ) :
    (expPoly x n : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ i / (i.factorial : ℝ) := by sorry
