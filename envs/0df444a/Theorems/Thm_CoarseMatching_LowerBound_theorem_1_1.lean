-- Prove2me | Theorems.Thm_CoarseMatching_LowerBound_theorem_1_1
-- name    : CoarseMatching.LowerBound.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:59.742413+00:00
-- url     : https://prove2.me/theorems/00199928-ff79-4c4b-9430-4765d5da0d23
-- title:
--   Theorem 1.1 — Nearly linear space for coarse matching estimates
-- statement:
--   There is an absolute constant $K>0$. For every $0<\varepsilon<1$ there are $b_\varepsilon>0$ and $n_\varepsilon$ such that for every integer $n\ge n_\varepsilon$, every real approximation factor $1\le c\le n^{\varepsilon/K}$, every integer pass count $1\le p\le n^{\varepsilon/K}$, and every randomized $p$-pass $S$-bit estimator, correctness with probability at least $2/3$ on every valid simple bipartite stream with public bipartition implies
--
--   $$S\ge b_\varepsilon n^{1-\varepsilon}.$$
--
--   Correctness is the full two-sided event $\operatorname{mm}(G)/c\le\widehat v\le c\operatorname{mm}(G)$. The bound holds in edge arrival and vertex arrival. The constants depend only on $\varepsilon$, not on $c,p,S$, the algorithm or the arrival mode. All sufficiently large integers $n$, including odd $n$, and zero-bit machines are included.
--
--   This is the sole goal theorem. The submission proves it with absolute witness $K=16$; the formal target preserves its existential form.
--
--   Differences from the source:
--   - encoding: Ω_ε(n^(1-ε)) for all sufficiently large n → positive b_ε and integer n_ε before n,c,p,S,algorithm and arrival mode; reason: the ordinary uniform meaning of the asymptotic lower bound
--   - encoding: simple bipartite n-vertex graph streams with a known bipartition → Fin n labels, a supplied Boolean bipartition, and duplicate-free insertion or vertex lists; reason: every source graph and order has this labeling; correctness on duplicate-free streams also follows for algorithms supporting repeated insertions
--   - generalization: S-bit multipass streaming algorithms → input-local transition kernels with a free public pass index and arbitrary real output laws; reason: every ordinary algorithm embeds by charging retained data and random bits to the state; the public pass index is known in the source simulation
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), Theorem 1.1, printed p. 1 (PDF p. 2). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_Streaming

namespace CoarseMatching.LowerBound

/-- Gillat Kol, STOC 2027 submission #1135 (October 2026), Theorem 1.1,
printed p.1 / PDF p.2. The absolute K precedes epsilon; b and n₀ are uniform in
n, real c, passes, space, algorithm and arrival mode. S=0 and odd n are included. -/
theorem theorem_1_1 :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ b : ℝ, 0 < b ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∀ (c : ℝ) (p S : ℕ) (A : Estimator n S) (mode : Arrival),
          1 ≤ c → c ≤ (n : ℝ) ^ (ε/K) →
          1 ≤ p → (p : ℝ) ≤ (n : ℝ) ^ (ε/K) →
          Correct A mode p c false → b * (n : ℝ) ^ (1-ε) ≤ (S : ℝ) := by sorry

end CoarseMatching.LowerBound
