-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_eq_3_3
-- name    : ConsumerUtilityApprox.UnitDemand.eq_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:54:30.626534+00:00
-- url     : https://prove2.me/theorems/bc819a74-9fe7-49c7-9b50-555c7d39f17f
-- title:
--   Equation (3.3) — the variation term is bounded by the total deletion loss
-- statement:
--   Let $V=(V_1,\dots,V_m)$ be a buyer's type with independent coordinates $V_j\ge0$, $0<\mathbb E[V_j]<\infty$, and let $W$ be an independent copy of $V$. Let $(x,p)$ be a truthful, individually rational single-buyer mechanism with nonnegative payments and allocations in $[0,1]^m$, with utility $u(v)=v\cdot x(v)-p(v)$, and let $D=\sum_jD_j$, $D_j=\mathbb E_V[u(V)-u(V_{-j},0)]$, be its total expected deletion loss. Then
--   $$\tfrac12\,\mathbb E_{V,W}\big[|u(V)-u(W)|\big]\le D .$$
--   This bounds the variation term of the decomposition (3.1) of $\mathbb E[u(V)]$; with Lemma 1 it gives the single-buyer bound (3.8) used in Lemma 5.
--
--   Differences from the source:
--   - reading: a single-buyer mechanism of §3 (unit-demand or constrained-additive; p. 13: the bounds need no unit demand) → any mechanism with x(b) ∈ [0,1]^m, no unit-demand clause; reason: §3 states these bounds for every feasible outcome set F ⊆ [0,1]^m (Theorem 1's setting); unit demand is a special case
--   - reading: expectations E[x_j(V)], E[u(V)] of a single-buyer mechanism (rules tacitly measurable) → IsTruthfulIRNPT includes Borel measurability of x and p; reason: the standing convention without which the source's expectations are undefined
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 10, equation (3.3) (proved in Appendix A, p. 33, (A.1))

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem eq_3_3 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) :
    (1 / 2 : ℝ) * ∫ vw, |buyerPayoff M vw.1 - buyerPayoff M vw.2| ∂((vecLaw G).prod (vecLaw G))
      ≤ totalDeletionLoss (vecLaw G) M := by sorry

end ConsumerUtilityApprox.UnitDemand
