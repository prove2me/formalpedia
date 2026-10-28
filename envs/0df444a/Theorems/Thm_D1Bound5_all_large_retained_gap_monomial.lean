-- Prove2me | Theorems.Thm_D1Bound5_all_large_retained_gap_monomial
-- name    : D1Bound5.all_large_retained_gap_monomial
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:55.801985+00:00
-- url     : https://prove2.me/theorems/bf6b1fbe-dd4c-49c1-8a45-95150bc47357
-- title:
--   All large retained gap monomial
-- statement:
--   The retained H48 coefficient yields the exact monomial growth used throughout the no-small-entry overlap table. Its hypotheses are the retained gap estimate itself and the elementary bounds on its normalized Vandermonde parameter; the analytic retained estimate is a separate theorem.
-- source:
--   D1Bound5/AllLargeOverlapConstants.lean, lines 84-127, SHA-256 1ecfa6ec2be53bcc4be16c181743e15299183cf147454f6adf4697f119eaefb4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

section
namespace D1Bound5








theorem _root_.D1Bound5.all_large_retained_gap_monomial
    (A B S C Q : ℝ) (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 0 < S)
    (hQ : 0 < Q) (hQ8 : Q ≤ 8)
    (hgap :
      3 ^ 5 * ((9999 / 10000) * (200 / 19) ^ 2) *
          (1 / Q - (51051 / 400000) / (A ^ 2 * B ^ 2)) ^ 2 *
          (A ^ 7 * B ^ 5 * S ^ 3) < C) :
    400 * (A ^ 7 * B ^ 5 * S ^ 3) < C := by sorry

end D1Bound5
end
