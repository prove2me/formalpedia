-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_lemma_5
-- name    : ConsumerUtilityApprox.UnitDemand.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:55:27.83931+00:00
-- url     : https://prove2.me/theorems/c388482e-6a47-4d45-9f74-450271c219fa
-- title:
--   Lemma 5 — a posted-price/free-lottery mixture beats every comparator in utility minus allocation cost, with factor 1/(2 + e/(e − 1))
-- statement:
--   Let a buyer have independent item values $V_j\sim G_j$ on $[0,\infty)$, $0<\mathbb E[V_j]<\infty$, and let $\lambda=(\lambda_1,\dots,\lambda_m)\ge0$ be demand weights. There is a BIC, ex-post individually rational single-buyer unit-demand randomized mechanism $M$ with nonnegative payments and measurable allocation and payment rules such that for every BIC, individually rational single-buyer unit-demand mechanism $C$ with nonnegative payments,
--   $$U(M)-\sum_j\lambda_jq^{\mathrm{alloc}}_j(M)\ \ge\ \frac{U(C)}{2+e/(e-1)}-\sum_j\lambda_jq^{\mathrm{alloc}}_j(C).$$
--   $M$ is chosen before $C$. Here $U$ and $q^{\mathrm{alloc}}$ are computed from reduced forms; ex-post IR means every realized outcome gives the truthful buyer nonnegative utility. Applied to each buyer with Lagrange multipliers, it gives the Lagrangian bound (5.2).
--
--   Differences from the source:
--   - encoding: values in R_+, laws F_j, items 1..m → ℝ≥0, ProbabilityMeasure ℝ≥0, Fin m; product law vecLaw; reason: Lean conventions for the same objects
--   - reading: expectations E[x_j(V)], E[u(V)] of a single-buyer mechanism (rules tacitly measurable) → IsTruthfulIRNPT includes Borel measurability of x and p; reason: the standing convention without which the source's expectations are undefined
--   - encoding: a randomized single-buyer mechanism M_i with realized outcomes → SBRand m: for each report a PMF over (item or none, payment); reason: ex-post IR needs realized outcomes; the paper's M_i uses finitely many random choices
--   - encoding: the comparator's BIC and IR (single buyer) → IsIC and IsIR of a Mechanism (Fin m), with IsUnitDemand; reason: for one buyer interim and ex-post reports coincide
--   - reading: the constructed mechanism M_i (its U(M_i) and q^alloc_ij(M_i) are expectations, rules tacitly measurable) → M.reduced satisfies IsMeasurableMech; reason: the standing convention without which U(M_i) and q^alloc(M_i) are undefined; without it a non-measurable allocation rule would make qAlloc the junk value 0 and erase M's allocation cost
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 19, Lemma 5 (proof pp. 20–24)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem lemma_5 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j) :
    ∃ M : SBRand m, M.IsBIC ∧ M.IsExPostIR ∧ M.HasNonnegPayments ∧ IsMeasurableMech M.reduced ∧
      ∀ C : Mechanism (Fin m), IsTruthfulIRNPT C → IsUnitDemand C →
        utility (vecLaw G) C / (2 + Real.exp 1 / (Real.exp 1 - 1))
            - ∑ j, lam j * qAlloc (vecLaw G) C j
          ≤ utility (vecLaw G) M.reduced - ∑ j, lam j * qAlloc (vecLaw G) M.reduced j := by sorry

end ConsumerUtilityApprox.UnitDemand
