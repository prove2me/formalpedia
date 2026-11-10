-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_6
-- name    : CNFLearnMQ.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:39.380243+00:00
-- url     : https://prove2.me/theorems/069aaf30-d090-4301-a9eb-de6f0f293441
-- title:
--   Lemma 5.6 — at most $2^{4dk^2}n$ seeds
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Let $G$ be a graph on the $n$ variables with maximum degree at most $dk$ (for instance a core dependency graph $G_{\mathcal R}$). The number of distinct seeds — signed subclauses $(S,\sigma_S)$ with $S$ a connected vertex set of $G$ of size $\lceil k/(t+1)\rceil$ — is at most
--   $$2^{4dk^2}\,n.$$
--
--   This linear bound on the initial queue is what removes the $n^k$ factor from the running time.
--
--   Differences from the source:
--   - generalization: a core dependency graph $G_{\mathcal R}$ with maximum degree at most $dk$ → every graph on the $n$ variables with maximum degree at most $dk$; reason: the proof uses only the degree bound; $G_{\mathcal R}$ is such a graph
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.6, p.23

import Mathlib
import Definitions.Def_CNFLearnMQ_buildSeedQueue

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.6, p.23 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Fix `t ≥ 1` (with the standing `k ≥ 100`, `d ≥ 1` and (3) of §5).
For every graph on the `n` variables with maximum degree at most `dk`, the number of distinct seeds
(signed subclauses on a connected vertex set of size `⌈k/(t + 1)⌉`) is at most `2^{4dk²}·n`.

**Formalization Note** The paper states this for a core dependency graph `G_R`; the proof uses only
the degree bound, and the statement here is for every graph with maximum degree at most `dk`. -/
theorem lemma_5_6 {n k d : ℕ} {t : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (hLLL : LLLCondition k d t) (hn : k ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.maxDegree ≤ d * k) :
    (seeds G (seedSize k t)).card ≤ 2 ^ (4 * d * k ^ 2) * n := by sorry

end CNFLearnMQ
