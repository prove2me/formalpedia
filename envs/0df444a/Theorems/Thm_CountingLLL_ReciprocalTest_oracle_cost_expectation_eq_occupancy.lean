-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_oracle_cost_expectation_eq_occupancy
-- name    : CountingLLL.ReciprocalTest.oracle_cost_expectation_eq_occupancy
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:29:03.672384+00:00
-- url     : https://prove2.me/theorems/8c3ec1d6-b6b0-411f-8f8c-133665835b30
-- title:
--   Operational expected oracle cost as phase occupancies
-- statement:
--   For the operational ReciprocalTest program, the extended expected number of oracle calls is the sum, over all execution steps, of the probabilities that the program is in an oracle-query phase. This includes nonterminating executions, for which the defined oracle cost is infinite.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5. This is an operational occupancy identity used toward the expected oracle-call bound, not the bound itself.

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.oracle_cost_expectation_eq_occupancy (B : ℝ≥0∞) :
    ∫⁻ ω, oracleCost ω ∂(entropyLaw B) = ∑' t, entropyLaw B {ω | ∃ k : Context, (run ω t).phase = .coinOracle k} := by sorry
