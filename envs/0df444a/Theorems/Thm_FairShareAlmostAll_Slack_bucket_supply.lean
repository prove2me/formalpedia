-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_bucket_supply
-- name    : FairShareAlmostAll.Slack.bucket_supply
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:40.53419+00:00
-- url     : https://prove2.me/theorems/aaab2e82-ac66-4c80-b063-a4cc362e4000
-- title:
--   Claim 2.2 — Bucket growth and ordinary supply
-- statement:
--   The construction has $m\ge q^2$ and $H\ge2$. The least positive bucket count exists, its buckets cover the goods and are nonempty, and every buffer contains exactly the requested number of goods. Moreover,
--   $$|C_j|\le(1+2/q)|C_{j-1}|\ (2\le j\le H),\qquad |S_h|\ge(1-3/q)|C_h|\ (1\le h<H).$$
--   The last bucket may be short. Explicit least-index, coverage and cardinality conclusions make the source's well-definedness assertion operational.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - encoding: the buffer sets are well-defined in the preceding bucket construction → least-index, coverage, nonempty buckets and exact buffer cardinalities are explicit conclusions; reason: these are structural well-definedness obligations of the prescribed construction, not additional hypotheses
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 8 (PDF p. 9), Claim 2.2; Appendix A, printed p. 27 (PDF p. 28); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

namespace FairShareAlmostAll.Slack

theorem bucket_supply {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q) :
    q^2 ≤ m ∧ 2 ≤ bucketCount q m ∧
    m ≤ prefixSize q (bucketCount q m) ∧
    (∀ k, 0 < k → k < bucketCount q m → prefixSize q k < m) ∧
    ((Finset.Icc 1 (bucketCount q m)).biUnion (bucket q m) = Finset.univ) ∧
    (∀ j ∈ Finset.Icc 1 (bucketCount q m),
      0 < (bucket q m j).card ∧
      (buffer q m j).card = (bucket q m j).card / q) ∧
    (∀ j ∈ Finset.Icc 2 (bucketCount q m),
      ((bucket q m j).card : ℝ) ≤ (1 + 2 / (q : ℝ)) * (bucket q m (j - 1)).card) ∧
    (∀ j ∈ Finset.Ico 1 (bucketCount q m),
      (1 - 3 / (q : ℝ)) * (bucket q m j).card ≤ (ordinaryBucket q m j).card) := by sorry

end FairShareAlmostAll.Slack
