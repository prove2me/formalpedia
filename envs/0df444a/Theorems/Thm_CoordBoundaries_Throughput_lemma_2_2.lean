-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_lemma_2_2
-- name    : CoordBoundaries.Throughput.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:09.43937+00:00
-- url     : https://prove2.me/theorems/a370df75-e1e7-4eb5-859d-ba0f757c0a0f
-- title:
--   Lemma 2.2 — consistent joint sampling for a noncrossing family of boundary edges
-- statement:
--   Fix a configuration solution of the relaxation and a set $J$ of global jobs whose boundary edges are noncrossing.
--
--   1. If the full consistency constraints hold, there is a joint law of one configuration $C_B$ per block with
--   $$\Pr[C_B=C]=x_{B,C}\qquad (B\in\mathcal B,\ C\in\mathcal C(B))$$
--   such that no job $j\in J$ belongs to both $C_{B_L(j)}$ and $C_{B_R(j)}$.
--   2. If the projected consistency constraints hold on the same $x$, the same conclusion holds provided every job of $J$ satisfies $j\in H_{B_L(j)}\cap H_{B_R(j)}$.
--
--   This is the coordination step of Algorithm 1: it lets the second output avoid duplicate boundary selections of the coordinated jobs while keeping every block's distribution.
--
--   **Formalization Note** Jobs and blocks have finite index types; expectations are finite weighted sums over the explicitly defined sampling outcomes.
--
--   Differences from the source:
--   - reading: "permit jointly sampling one configuration C_B per block" → there exists a probability distribution on outcomes (one configuration per block) with the stated marginals and separation on its support; reason: a sampling procedure defines such a distribution and every such distribution can be sampled
--   - generalization: a feasible solution of the full relaxation, including the density constraints and η = 1/q ≤ 1/100 → the density constraints and η are not assumed; reason: the proof uses only the consistency equations and the distributions x_B; every source solution satisfies the hypotheses
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines, a zero configuration cap; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 13, Lemma 2.2

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Relaxation

open Classical

namespace CoordBoundaries.Throughput

/-- **Lemma 2.2** (Tong–Xu, p. 13). Fix a set `J` of global jobs whose boundary edges are
noncrossing. Under the full consistency constraints there is a joint law of one configuration per
block with `Pr[C_B = C] = x_{B,C}` such that no job of `J` belongs to both `C_{B_L(j)}` and
`C_{B_R(j)}`. Under projected consistency (on the same `x`), the same holds if every job of `J` is
tracked at both of its boundary blocks. -/
theorem lemma_2_2 {I : Instance} (hI : I.Valid) {P : Partition I.T} {K : ℕ}
    (s : ConfigSol I P K) :
    (∀ π, s.FullConsistent π → ∀ J : Finset (Fin I.n), (∀ j ∈ J, P.IsGlobal j) →
        P.Noncrossing J →
        ∃ μ, IsLaw P K μ ∧ s.HasMarginals μ ∧ Separates P μ J) ∧
    (∀ H π, s.ProjConsistent H π → ∀ J : Finset (Fin I.n), (∀ j ∈ J, P.IsGlobal j) →
        P.Noncrossing J →
        (∀ j ∈ J, j ∈ trackedAt H (P.BL j) ∧ j ∈ trackedAt H (P.BR j)) →
        ∃ μ, IsLaw P K μ ∧ s.HasMarginals μ ∧ Separates P μ J) := by sorry

end CoordBoundaries.Throughput
