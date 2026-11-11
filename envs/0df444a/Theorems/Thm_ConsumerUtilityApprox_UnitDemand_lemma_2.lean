-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_lemma_2
-- name    : ConsumerUtilityApprox.UnitDemand.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:54:27.578719+00:00
-- url     : https://prove2.me/theorems/93d20842-45a9-4d08-af48-b1062c2baed8
-- title:
--   Lemma 2 — the deletion loss of an item is at most the single-item ex-ante-constrained optimum
-- statement:
--   Let $V$ be a buyer's type with independent coordinates $V_j\sim G_j$ on $[0,\infty)$, $0<\mathbb E[V_j]<\infty$. Let $(x,p)$ be a truthful, individually rational single-buyer mechanism with nonnegative payments and allocations in $[0,1]^m$, utility $u$, and let $q_j\ge\mathbb E[x_j(V)]$. Then for every item $j$
--   $$D_j=\mathbb E_V\big[u(V)-u(V_{-j},0)\big]\le\mathrm{OPT}^{1,1}(V_j;q_j),$$
--   where $\mathrm{OPT}^{1,1}$ is the supremum of $\mathbb E[V_ja(V_j)-\tau(V_j)]$ over BIC, IR single-dimensional mechanisms with nonnegative payments and $\mathbb E[a(V_j)]\le q_j$. It reduces the variation term to single-item problems.
--
--   Differences from the source:
--   - reading: a single-buyer mechanism of §3 (unit-demand or constrained-additive; p. 13: the bounds need no unit demand) → any mechanism with x(b) ∈ [0,1]^m, no unit-demand clause; reason: §3 states these bounds for every feasible outcome set F ⊆ [0,1]^m (Theorem 1's setting); unit demand is a special case
--   - reading: expectations E[x_j(V)], E[u(V)] of a single-buyer mechanism (rules tacitly measurable) → IsTruthfulIRNPT includes Borel measurability of x and p; reason: the standing convention without which the source's expectations are undefined
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
--   - encoding: OPT^{1,1} defined as a max (2.3) → OPT11 is the supremum (sSup); attainment is the separate item posted_price_representation; reason: an upper bound by the supremum is the same as by the maximum once the maximum exists
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 12, Lemma 2

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem lemma_2 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (q : Fin m → ℝ) (hq : ∀ j, qAlloc (vecLaw G) M j ≤ q j) (j : Fin m) :
    deletionLoss (vecLaw G) M j ≤ OPT11 (G j) (q j) := by sorry

end ConsumerUtilityApprox.UnitDemand
