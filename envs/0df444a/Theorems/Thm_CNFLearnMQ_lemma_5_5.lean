-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_5
-- name    : CNFLearnMQ.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:18:04.188426+00:00
-- url     : https://prove2.me/theorems/04405cfd-1ca1-4451-811a-ef0d3ee9675e
-- title:
--   Lemma 5.5 — every clause meets a large connected piece of $G_{\mathcal R}$
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Fix $\delta\in(0,1)$. Let $X_1,\dots,X_N$ be independent samples from $\mu_\Phi$ and let $G_{\mathcal R}$ be the core dependency graph of $\mathcal R=\bigcup_i\mathcal R_{X_i}$. If
--   $$N\ge k\left\lceil\log\frac{dkn}{\delta}\right\rceil,$$
--   then with probability at least $1-\delta$, for every clause $c\in C$ the induced subgraph $G_{\mathcal R}[\mathrm{vbl}(c)]$ contains a connected component with at least $\lceil k/(t+1)\rceil$ vertices.
--
--   This is why the seeds, which are much fewer than the $\Theta(n^k)$ candidate clauses of Valiant's algorithm, still contain a subclause of every target clause.
--
--   Differences from the source:
--   - encoding: $G_{\mathcal R}[\mathrm{vbl}(c)]$ contains a connected component with at least $s$ vertices → some $T\subseteq\mathrm{vbl}(c)$ with $|T|\ge s$ induces a connected subgraph of $G_{\mathcal R}$; reason: a component is such a $T$, and such a $T$ lies inside one component; equivalent
--   - encoding: $N$ independent samples → the law `iidList` of a list of $N$ independent draws; reason: same distribution
--   - encoding: $\mu_\Phi$, defined when $\Omega(\Phi)\ne\emptyset$ (p.13); under (3) $\Phi$ is satisfiable by Theorem 3.1 → nonemptiness of the solution set is a hypothesis `h`; reason: the published law `solutionLaw` needs the proof; under the standing assumptions it always holds, so no instance is excluded
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.5, pp.21–22

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.5, p.21 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Fix `t ≥ 1` and `δ ∈ (0, 1)`, let `k ≥ 100`, `d ≥ 1` and let `Φ` be an
`n`-variable `(k, d)`-CNF satisfying (3), `n ≥ k`. Let `X_1, …, X_N` be independent samples from
`µ_Φ` and `G_R` the core dependency graph of their exact core families. If
`N ≥ k⌈log(dkn/δ)⌉` (base-2 logarithm), then with probability at least `1 − δ`, for every `c ∈ C`,
`G_R[vbl(c)]` contains a connected component with at least `⌈k/(t + 1)⌉` vertices.

**Formalization Note** "`G_R[vbl(c)]` contains a connected component with at least `s` vertices"
is written as "some `T ⊆ vbl(c)` with `|T| ≥ s` induces a connected subgraph of `G_R`" (a
component is such a `T`, and such a `T` lies inside one component). `µ_Φ` exists only when
`Ω(Φ) ≠ ∅`, so nonemptiness is a hypothesis (it always holds under (3), Theorem 3.1). -/
theorem lemma_5_5 {n k d : ℕ} {t δ : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (Φ : CNF n) (hΦ : KD Φ k d) (h : (solutions Φ).Nonempty)
    (N : ℕ) (hN : k * ⌈log₂ ((d : ℝ) * k * n / δ)⌉₊ ≤ N) :
    ENNReal.ofReal (1 - δ) ≤ prob (iidList (solutionPMF Φ h) N) (fun Xs =>
      ∀ c ∈ Φ, ∃ T : Finset (Fin n), T ⊆ support c ∧ seedSize k t ≤ T.card ∧
        IsConnectedSet (coreGraph (coreUnion Φ Xs)) T) := by sorry

end CNFLearnMQ
