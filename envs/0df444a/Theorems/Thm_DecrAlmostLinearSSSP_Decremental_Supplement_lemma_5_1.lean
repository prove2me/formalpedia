-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Supplement_lemma_5_1
-- name    : DecrAlmostLinearSSSP.Decremental.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:18:35.113203+00:00
-- url     : https://prove2.me/theorems/3d479d6a-b61a-456a-b8ed-3ffd7a0d3d27
-- title:
--   Lemma 5.1 — Black-box incremental simple-path reporting
-- statement:
--   There are one deterministic scalar arithmetic program and absolute constants $C>0$ and $Q,P_0\in\mathbb N_{>0}$ with the following property. Let $m\ge n\ge2$, let $W\ge1$ be real, start with an empty directed graph with real edge weights in $[1,W]$, fix a source $s$, and insert at most $m$ edges. For any real $\delta\in(0,1)$, put $H=\lceil\log_2(m+1)\rceil$. Suppose an external oracle has nonincreasing estimates $a_t(s)=0$, is infinite exactly at unreachable nonsource vertices, and has finite nonsource values in $\{(1+\delta)^k:k\in\mathbb N\}$ with
--
--   $$
--   d_t(v)\le a_t(v)\le(1+\delta)^2d_t(v).
--   $$
--
--   After every insertion it supplies exactly one batch of all nonsource vertices whose estimates strictly decrease, including those newly reachable. Uniformly over every such oracle trace and batch ordering, all reduction calls terminate and maintain nonincreasing labels, finite exactly on reachable vertices, satisfying
--
--   $$
--   d_t(v)\le\ell_t(v)\le(1+\delta)^{2(H+1)}d_t(v),\qquad
--   T_{\mathrm{maintenance}}\le C\delta^{-1}m\log_2m\log_2n\log_2(nW).
--   $$
--
--   For every reachable vertex the program emits a simple source path of weight at most $\ell_t(v)$ in at most $P_0|P|$ scalar work, where $|P|$ counts vertices. Label and unreachability queries take at most $Q$ work. All guarantees include initialization and every completed update boundary. Maintenance includes consuming the reports and all reduction work; it excludes the external oracle's own computation and subsequent client query costs.
--
--   The lemma converts an estimate interface into simple paths and supports Theorem 1.2. Its proof bounds the report count at a vertex by $q_v\le3+\lceil\log(nW)/\log(1+\delta)\rceil$ and the number of repairs containing it by $(H+1)q_v$ (pp.34–35). No integer-weight or polynomial-weight restriction is imported into this black-box result, and $\delta$ is arbitrary rather than the later chosen split parameter.
--
--   **Formalization Note** The input's accuracy field denotes $\delta$, and the Lean output-work constant is named $P$. The oracle is a specification of completed estimates and exact report sets; only current reported finite values are supplied on the input tape. Correctness, monotonicity, path simplicity, termination and the budget are conclusions of the reduction statement.
--
--   Differences from the source:
--   - encoding: finite directed graph with original positive edge weights and active insertion prefixes → Fin-indexed original edge identifiers with legal disjoint initial and insertion lists and extended nonnegative walk distance; reason: preserves all finite directed instances including parallel edges and entering-source edges; finite weights are embedded in ENNReal and empty feasible walk sets have distance infinity
--   - encoding: deterministic unit-cost data structure with explicit maintained entries and query operations → one finite scalar arithmetic program with prefix-only input, actual terminating executions, explicit memory cells, preserved query memory and charged input delivery; reason: fixes the execution and array layout without assuming correctness, termination or a fast implementation; uniform constants absorb the fixed 32-unit interface charges
--   - encoding: simple path reported in O(|P|), counting vertices including the source → a directed active original-edge walk with duplicate-free vertex list, whose entire vertex/edge transcript is emitted by scalar stores within P(|edges|+1) work; reason: preserves the output-linear guarantee and charges source-only paths, traversal, reversal and emission; there is no unit-cost path oracle
--   - encoding: exact oracle report batch and O(δ^(-1)m log m log n log(nW)) maintenance → arbitrary duplicate-free ordering of the exact decrease set, delivered with its new finite values, and a uniform positive C multiplying the same base-two logarithmic product; reason: a batch is a set of changed vertices; ordering is arbitrary, all consumption is charged, and changing log bases alters only the absolute constant
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p.31, Lemma 5.1; pp.32–35, algorithm, correctness and cost

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Guarantees

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

/-- Lemma 5.1, p.31. Real weights in [1,W], arbitrary δ in (0,1), and every conforming
oracle trace. Only delivery and the reduction's executed instructions are charged here;
there is no oracle hypothesis in the companion Theorem 1.2. -/
theorem lemma_5_1 :
    ∃ (p : Program) (C : ℝ) (Q P : ℕ), 0 < C ∧ 0 < Q ∧ 0 < P ∧
      ∀ i : Instance, i.Valid → 2 ≤ i.n → i.initial = [] → i.accuracy < 1 →
        ∀ es : List (Fin i.k), i.Legal es → ∀ o : OracleTrace i, o.Valid es →
          ∃ cs : List Machine,
            Run p i o.batches es cs ∧
            PathStates p i es cs ((1 + i.accuracy) ^ (2 * (height i.size + 1))) Q P ∧
            NonincreasingLabels i cs ∧
            WithinBudget i o.batches es cs (reductionBudget C i) := by sorry

end DecrAlmostLinearSSSP.Decremental.Supplement
