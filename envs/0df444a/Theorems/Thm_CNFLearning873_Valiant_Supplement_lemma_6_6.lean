-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_lemma_6_6
-- name    : CNFLearning873.Valiant.Supplement.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:41:51.444725+00:00
-- url     : https://prove2.me/theorems/0d15a3c5-6fc1-4e11-9b4a-8719b53e7304
-- title:
--   Lemma 6.6 (used in the proof of Theorem 6.5) — count and solution-sampling oracle calls
-- statement:
--   For each $k\ge3$, there are constants $A_k>0$ and $n_0(k)\ge3$ such that for $n\ge n_0(k)$ every count expansion and every conditional-count solution sampler uses at most
--
--   $$\exp\left(A_k\frac n{\log_2n}\right)$$
--
--   calls to the exact counting oracle. Here $S$ is a list drawn from a family of width-$k$ clauses, and counts use the strict multiplicity threshold $\sum_{c\in J}\mathrm{mult}_S(c)<r$, where $r=n/(\log_2n)^2$. Extra query clauses may be supplied, as in the greedy and prefix cases. The estimate applies to every supported report for every rejection limit. The sampler uses one conditional count per variable with a carried total; abort can only stop further calls. This is the oracle-call estimate used in Theorem 6.5.
--
--   Differences from the source:
--   - encoding: Boolean assignments on a named n-variable set → assignments on Fin n, using the published CNF and nonempty uniform-solution laws; reason: variable relabeling changes no instance; output satisfiability prevents an undefined uniform law
--   - generalization: the algorithm calls counts and samplers on sampled multisets with greedy or prefix extras → any finite list of width-k clauses, arbitrary extra query clauses, any carried sampler total and any rejection limit; reason: the enumerated case count depends only on the clause support and r, not on multiplicity magnitudes, extra clauses, the carried total or cutoff; all source calls specialize to these programs
--   - encoding: exp(O_k(n/log n)) calls → positive k-only exponential coefficient and threshold, with a per-supported-report call count; reason: counts the actual query list for every execution; early rejection can only decrease it
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Lemma 6.6, printed p.28 = 1-based PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_OracleLearner

namespace CNFLearning873.Valiant.Supplement

/-- Lemma 6.6, pp.28-29 = PDF pp.28-29. These are the actual count-expansion and
chain-rule sampling programs; extras allow both greedy clauses and conditional units. -/
theorem lemma_6_6 (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∀ C : CNF n, (∀ c ∈ C, width c = k) →
    ∀ S : List (Clause n), (∀ c ∈ S, c ∈ C) →
    ∀ extras : CNF n, ∀ L : ℕ,
      (∀ z, implemented L (countThreshold (radius n) S extras) z ≠ 0 →
        (z.queries.length : ℝ) ≤ Real.exp (A * oracleExponent n)) ∧
      (∀ total : ℕ, ∀ z, implemented L (sampleThreshold (radius n) S total) z ≠ 0 →
        (z.queries.length : ℝ) ≤ Real.exp (A * oracleExponent n)) := by sorry

end CNFLearning873.Valiant.Supplement
