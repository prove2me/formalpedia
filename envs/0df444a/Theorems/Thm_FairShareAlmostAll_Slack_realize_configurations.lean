-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_realize_configurations
-- name    : FairShareAlmostAll.Slack.realize_configurations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:35.0072+00:00
-- url     : https://prove2.me/theorems/d7608cad-525f-4f53-981b-61b6a2cac0bc
-- title:
--   Lemma 2.1 — Realizing selected configurations
-- statement:
--   Let $I\subseteq N_+$ and select a configuration $P_i$ for each $i\in I$ satisfying $\sum_{i\in I}d_{j,iP_i}\le|S_{j-1}|$ for $2\le j\le H$. There are pairwise disjoint partial bundles with
--   $$B_i\subseteq S\cup E,\qquad u_i(B_i)\ge u_i(P_i)\quad(i\in I).$$
--   Every good in $R$, $S_H$ and $E_H$ remains unused. The guarantee retains the whole configuration value, which may exceed one; the empty selected set is allowed.
--
--   Differences from the source:
--   - encoding: arbitrary finite goods and bundle families → Fin-indexed goods and explicit finite probability laws; reason: finite relabeling preserves all values, prices, distributions and allocation constraints, including empty goods
--   - encoding: bundles indexed only by I → bundles indexed by all agents, empty outside I; reason: empty extension is exactly a partial allocation for I and adds no constraint on selected agents
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 9 (PDF p. 10), Lemma 2.1, equation (2); Appendix A, printed pp. 28–30 (PDF pp. 29–31); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

namespace FairShareAlmostAll.Slack

theorem realize_configurations {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (I : Finset (Fin n)) (hI : I ⊆ active X) (P : Fin n → Finset (Fin m))
    (hP : ∀ i ∈ I, Configuration X q i (P i))
    (hrequests : ∀ j ∈ Finset.Icc 2 (bucketCount q m),
      ∑ i ∈ I, request X q j i (P i) ≤ (ordinaryBucket q m (j - 1)).card) :
    ∃ B : Fin n → Finset (Fin m), PartialAllocation B ∧
      (∀ i, i ∉ I → B i = ∅) ∧
      (∀ i ∈ I, cappedValue X i (P i) ≤ cappedValue X i (B i)) ∧
      (∀ i ∈ I, B i ⊆ ordinary q m ∪ allBuffers q m) ∧
      ∀ i, Disjoint (B i) (reserve q m ∪ ordinaryBucket q m (bucketCount q m) ∪
        buffer q m (bucketCount q m)) := by sorry

end FairShareAlmostAll.Slack
