-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_lemma_1
-- name    : ConsumerUtilityApprox.UnitDemand.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:54:32.300358+00:00
-- url     : https://prove2.me/theorems/bc661d20-437b-4ef3-bf78-4874a4663e30
-- title:
--   Lemma 1 — the overlap term is bounded by a free-lottery term
-- statement:
--   Let $V$ be a buyer's type with independent coordinates $V_j\ge0$, $0<\mathbb E[V_j]<\infty$, and $W$ an independent copy. Let $(x,p)$ be a truthful, individually rational single-buyer mechanism with nonnegative payments and allocations in $[0,1]^m$, utility $u$, and ex-ante allocation probabilities $\mathbb E[x_j(V)]\le q_j$. For any $\ell_1,\dots,\ell_m\in(0,1]$,
--   $$\mathbb E_{V,W}\big[\min\{u(V),u(W)\}\big]\le \mathbb E_V\Big[\max_j\ell_jV_j\Big]\sum_j\frac{q_j}{\ell_j}.\qquad(3.4)$$
--   The right side is the utility of the best of the free lotteries $\ell_j$ times a total scaling weight; with (3.3) it gives (3.8).
--
--   Differences from the source:
--   - reading: a single-buyer mechanism of §3 (unit-demand or constrained-additive; p. 13: the bounds need no unit demand) → any mechanism with x(b) ∈ [0,1]^m, no unit-demand clause; reason: §3 states these bounds for every feasible outcome set F ⊆ [0,1]^m (Theorem 1's setting); unit demand is a special case
--   - reading: expectations E[x_j(V)], E[u(V)] of a single-buyer mechanism (rules tacitly measurable) → IsTruthfulIRNPT includes Borel measurability of x and p; reason: the standing convention without which the source's expectations are undefined
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 10, Lemma 1

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem lemma_1 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (q : Fin m → ℝ) (hq : ∀ j, qAlloc (vecLaw G) M j ≤ q j)
    (ℓ : Fin m → ℝ) (hℓ : ∀ j, 0 < ℓ j ∧ ℓ j ≤ 1) :
    ∫ vw, min (buyerPayoff M vw.1) (buyerPayoff M vw.2) ∂((vecLaw G).prod (vecLaw G))
      ≤ (∫ v, (⨆ j, ℓ j * (v j : ℝ)) ∂(vecLaw G)) * ∑ j, q j / ℓ j := by sorry

end ConsumerUtilityApprox.UnitDemand
