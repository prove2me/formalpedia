-- Prove2me | Theorems.Thm_FairShareAlmostAll_Slack_Supplement_random_realization
-- name    : FairShareAlmostAll.Slack.Supplement.random_realization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:15.699338+00:00
-- url     : https://prove2.me/theorems/ea3cf595-a75a-431e-8ef4-f4c9316485db
-- title:
--   Lemma 4.2 — Randomized realization with exact assignment probabilities
-- statement:
--   Work under the standing assumptions of Section 2 (integer $q\ge16$, $n\ge2$, $W\le1$, $b_i\le1/q^2$, nonempty $N_+$, ordered goods). Let $I\subseteq N_+$ and select a configuration $P_i$ for each $i\in I$ (a bundle with capped value $u_i(P_i)\ge1$ avoiding $C_1$) such that
--
--   $$\sum_{i\in I}d_{j,iP_i}\le|S_{j-1}|\qquad(2\le j\le H).$$
--
--   Then there is a randomized partial allocation $(B_i)$ which, in every outcome, satisfies all conclusions of Lemma 2.1: the bundles are pairwise disjoint, empty outside $I$, $u_i(B_i)\ge u_i(P_i)$ and $B_i\subseteq S\cup E$ for $i\in I$, and no bundle meets $R$, $S_H$ or $E_H$. Moreover, for every $i\in I$ and every good $g$,
--
--   $$\Pr(g\in B_i)=\begin{cases}\dfrac{d_{j,iP_i}}{|S_{j-1}|}, & g\in S_{j-1},\ 2\le j\le H,\\[2mm] \dfrac{1}{|E_{h_i}|}, & g\in E_{h_i},\ 1\le h_i<H,\\[2mm] 0, & \text{otherwise.}\end{cases}$$
--
--   Here $S_h$ is the ordinary part of bucket $C_h$, $E_h$ its buffer goods, $h_i$ the cutoff and $d_{j,iP}$ the request of Section 2. This randomized form of Lemma 2.1 controls every assignment probability exactly, which Proposition 4.1 uses to obtain ex-ante proportionality.
--
--   Differences from the source:
--   - encoding: bundles indexed only by $I$ → bundles indexed by all agents, empty outside $I$, under a `FiniteLaw` on bundle families; reason: empty extension is exactly a partial allocation for $I$; "in every outcome" is every family of positive weight
--   - encoding: the three cases of the displayed formula → three conjuncts, the last one stated for goods outside every $S_{j-1}$ ($2\le j\le H$) and outside $E_{h_i}$ when $1\le h_i<H$; reason: the ordinary buckets and buffers are disjoint, so this is exactly the source's case split
-- source:
--   Tomer Ezra, Tamar Garbuz, Fair Share Allocations for Almost All Agents, STOC 2027 submission #480 (October 2026), printed p. 15 (PDF p. 16), Lemma 4.2 (hypotheses of Lemma 2.1, printed p. 9, PDF p. 10, equation (2)); proof Appendix A, printed p. 30 (PDF p. 31); source.pdf SHA256 c9f47a54f6a9e1568951e8e3845ff79c34d51d391a68fd697d37d8ba29cc7491

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

theorem random_realization {n m : ℕ} (X : Instance n m) (q : ℕ)
    (h : ConstructionAssumptions X q)
    (I : Finset (Fin n)) (hI : I ⊆ active X) (P : Fin n → Finset (Fin m))
    (hP : ∀ i ∈ I, Configuration X q i (P i))
    (hrequests : ∀ j ∈ Finset.Icc 2 (bucketCount q m),
      ∑ i ∈ I, request X q j i (P i) ≤ (ordinaryBucket q m (j - 1)).card) :
    ∃ D : FiniteLaw (Fin n → Finset (Fin m)),
      (∀ B, 0 < D.weight B →
        PartialAllocation B ∧
        (∀ i, i ∉ I → B i = ∅) ∧
        (∀ i ∈ I, cappedValue X i (P i) ≤ cappedValue X i (B i)) ∧
        (∀ i ∈ I, B i ⊆ ordinary q m ∪ allBuffers q m) ∧
        ∀ i, Disjoint (B i) (reserve q m ∪ ordinaryBucket q m (bucketCount q m) ∪
          buffer q m (bucketCount q m))) ∧
      (∀ i ∈ I, ∀ j ∈ Finset.Icc 2 (bucketCount q m), ∀ g ∈ ordinaryBucket q m (j - 1),
        probability D (fun B => g ∈ B i) =
          request X q j i (P i) / ((ordinaryBucket q m (j - 1)).card : ℝ)) ∧
      (∀ i ∈ I, 1 ≤ cutoff X q i → cutoff X q i < bucketCount q m →
        ∀ g ∈ buffer q m (cutoff X q i),
          probability D (fun B => g ∈ B i) = 1 / ((buffer q m (cutoff X q i)).card : ℝ)) ∧
      ∀ i ∈ I, ∀ g : Fin m,
        (∀ j ∈ Finset.Icc 2 (bucketCount q m), g ∉ ordinaryBucket q m (j - 1)) →
        ¬ (1 ≤ cutoff X q i ∧ cutoff X q i < bucketCount q m ∧
            g ∈ buffer q m (cutoff X q i)) →
        probability D (fun B => g ∈ B i) = 0 := by sorry

end FairShareAlmostAll.Slack.Supplement
