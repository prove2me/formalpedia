-- Prove2me | Theorems.Thm_AnalyticEnclosures_log_le_of_expPoly
-- name    : AnalyticEnclosures.log_le_of_expPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/6f92b36a-75c2-483b-ac7c-d7494ffe3d8d
-- title:
--   AnalyticEnclosures: Log le of exp Poly
-- statement:
--   A rational lower Taylor witness proves an upper bound for the real log.
--
--   Rational Taylor certificates imply inequalities for the actual real logarithm and exponential. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/AnalyticEnclosures.lean#L25-L31). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/AnalyticEnclosures.lean#L25-L31 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

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

theorem AnalyticEnclosures.log_le_of_expPoly (q L : ℚ) (n : ℕ)
    (hq : 0 < q) (hL : 0 ≤ L) (certificate : q ≤ expPoly L n) :
    Real.log (q : ℝ) ≤ (L : ℝ) := by sorry
