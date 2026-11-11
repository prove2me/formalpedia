-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_lemma_3
-- name    : ConsumerUtilityApprox.UnitDemand.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:54:30.158328+00:00
-- url     : https://prove2.me/theorems/7b00bf50-9b2f-4855-b251-168ad3082f0a
-- title:
--   Lemma 3 — posting independent single-item prices together keeps the caps and a (1 − 1/e) fraction of single-item utility
-- statement:
--   Let $V_1,\dots,V_m$ be independent item values ($V_j\sim G_j$ on $[0,\infty)$, $0<\mathbb E[V_j]<\infty$) and $P_1,\dots,P_m$ independent prices, independent of the values, with laws $\pi_j$ on $[0,\infty]$ ($P_j=\infty$: item $j$ is not offered). Suppose $\Pr(V_j>P_j)\le q_j$ for each $j$ and $\sum_jq_j\le1$. Let $U(M^1_j)=\mathbb E[(V_j-P_j)^+]$, and let $M^{UD}$ post all prices together, the buyer taking an item of largest strictly positive surplus (ties uniform, no purchase otherwise) and paying its price. Then $M^{UD}$ allocates item $j$ with probability at most $q_j$, and
--   $$U(M^{UD})\ge\Big(1-\frac1e\Big)\sum_jU(M^1_j).$$
--   This recovers the deletion-loss part of the benchmark with a unit-demand mechanism.
--
--   Differences from the source:
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
--   - generalization: independent (possibly randomized) nonnegative prices P_j → independent price laws on [0, ∞], ∞ meaning no offer; reason: §2.3 and Lemma 5 apply the lemma to prices that may be infinite; finite prices are the special case of laws on [0, ∞)
--   - reading: the buyer chooses their utility-maximizing option → largest strictly positive surplus, ties uniform, no purchase at zero surplus; reason: tie rules of p. 7
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 14, Lemma 3

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem lemma_3 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (π : Fin m → Measure ℝ≥0∞)
    [∀ j, IsProbabilityMeasure (π j)] (q : Fin m → ℝ)
    (hq : ∀ j, saleProb1 (G j) (π j) ≤ q j) (hsum : ∑ j, q j ≤ 1) :
    (∀ j, udAlloc G π j ≤ q j) ∧
      (1 - Real.exp (-1)) * ∑ j, postedUtility1 (G j) (π j) ≤ udUtility G π := by sorry

end ConsumerUtilityApprox.UnitDemand
