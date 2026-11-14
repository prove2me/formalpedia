-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_oracle_cost_eq_query_steps
-- name    : CountingLLL.ReciprocalTest.oracle_cost_eq_query_steps
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:25:22.370197+00:00
-- url     : https://prove2.me/theorems/0d409a7b-0b4a-4878-818c-180cd6e13079
-- title:
--   Operational oracle cost equals the number of oracle-query steps
-- statement:
--   For every entropy tape, the full operational ReciprocalTest oracle cost equals the extended-nonnegative count of steps whose phase is an oracle query. On a nonhalting tape both quantities are infinite. This connects the operational cost observable to finite-time state probabilities.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.oracle_cost_eq_query_steps (ω : Entropy) :
    oracleCost ω = ∑' t, (match (run ω t).phase with | .coinOracle _ => (1:ℝ≥0∞) | _ => 0) := by sorry
