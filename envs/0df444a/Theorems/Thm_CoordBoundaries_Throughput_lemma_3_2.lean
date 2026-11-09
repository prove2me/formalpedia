-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_lemma_3_2
-- name    : CoordBoundaries.Throughput.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:25.207993+00:00
-- url     : https://prove2.me/theorems/a19a1374-1347-4d27-9acb-a1f21a2d544d
-- title:
--   Lemma 3.2 — crossing exchanges: E[A×] ≥ F − W + Σ (a_j b_j)(a_k b_k) − 8ηF
-- statement:
--   Fix a feasible solution of the relaxation (with stored schedules and both density constraints), $\eta=1/q\le1/100$ and $K\ge1$. Let $\mathcal X$ be a collection of crossing pairs of global jobs with no job in two pairs, fixed before the configurations are sampled. Then, for independent block sampling and $A_\times$ the size of a maximum job–slot matching,
--   $$\mathbb E[A_\times]\ge F-W+\sum_{\{j,k\}\in\mathcal X}(a_jb_j)(a_kb_k)-8\eta F.$$
--
--   This is the guarantee of the first output of Algorithm 1; the product terms are the gains from the crossing exchanges.
--
--   **Formalization Note** Jobs and blocks have finite index types; expectations are finite weighted sums over the explicitly defined sampling outcomes.
--
--   Differences from the source:
--   - encoding: a collection of unordered pairs {j, k} → a finite set of ordered pairs in which no job occurs in two pairs; reason: disjointness excludes listing a pair in both orders, so the sum is the same
--   - generalization: a solution of the full or projected consistent relaxation → the consistency constraints are not assumed; reason: independent sampling uses only x; consistent solutions satisfy the hypotheses
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 18, Lemma 3.2

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Rounding

open Classical

namespace CoordBoundaries.Throughput

/-- **Lemma 3.2** (Tong–Xu, p. 18). Fix a feasible relaxation solution with the density
constraints, `η = 1/q ≤ 1/100` and `K ≥ 1`. Let `𝒳` be a collection of crossing pairs of global
jobs with no job in two pairs, fixed before the configurations are sampled. Then, under
independent block sampling,
`E[A×] ≥ F − W + Σ_{{j,k} ∈ 𝒳} (a_j b_j)(a_k b_k) − 8ηF`. -/
theorem lemma_3_2 {I : Instance} (hI : I.Valid) {P : Partition I.T} {K Δ q : ℕ}
    (hq : 100 ≤ q) (hK : 1 ≤ K) (hΔ : 1 ≤ Δ) (s : ConfigSol I P K)
    (hD₁ : s.DenseBlocks Δ q) (hD₂ : s.DenseSuper q)
    (X : Finset (Fin I.n × Fin I.n)) (hX : P.IsCrossCollection X) :
    s.F - s.W + (∑ e ∈ X, (s.a e.1 * s.b e.1) * (s.a e.2 * s.b e.2)) - 8 * eta q * s.F ≤
      s.Eprod (fun ω => (s.Ax ω : ℝ)) := by sorry

end CoordBoundaries.Throughput
