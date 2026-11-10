-- Prove2me | Theorems.Thm_CoarseMatching_LowerBound_lemma_4_1
-- name    : CoarseMatching.LowerBound.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:37:32.410172+00:00
-- url     : https://prove2.me/theorems/4473eadb-147f-4f5c-80f2-1888c5d83d34
-- title:
--   Lemma 4.1 — Graph gap and estimator test consequence
-- statement:
--   For every admissible family of the shared-core graph laws, with $c\ge1$, $a=24c^2$, $1\le d\le h\le N/a$, Equation (4), and $a/N\to0$, both probabilities tend to one:
--
--   $$\Pr_{D_0}[\operatorname{vc}(G_0)\le3N/a]\to1,\qquad\Pr_{D_1}[\operatorname{mm}(G_1)\ge N/4]\to1.$$
--
--   Eventually, uniformly over all positive-pass estimators and both arrival modes satisfying Equation (1) on each legal simple bipartite stream, accepting precisely when $\widehat v>N/(8c)$ has acceptance gap at least $1/4$.
--
--   The final test consequence is the continuation on printed p.12. Both graph bounds and this consequence form one milestone.
--
--   Differences from the source:
--   - encoding: a=o(N) and probability 1-o(1) → arbitrary eventually admissible parameter families with a(N)/N tending to zero, probability limits equal to one, and eventual conclusions; reason: standard family quantifiers give every source regime; no small-N consequence or fixed special family is asserted
--   - encoding: simple bipartite n-vertex graph streams with a known bipartition → Fin n labels, a supplied Boolean bipartition, and duplicate-free insertion or vertex lists; reason: every source graph and order has this labeling; correctness on duplicate-free streams also follows for algorithms supporting repeated insertions
--   - generalization: S-bit multipass streaming algorithms → input-local transition kernels with a free public pass index and arbitrary real output laws; reason: every ordinary algorithm embeds by charging retained data and random bits to the state; the public pass index is known in the source simulation
--   - generalization: an estimator satisfying Equation (1) → correctness is needed only on the simple bipartite streams; reason: both hard graph laws are supported on that class, so the source claim is a direct instance
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), Lemma 4.1, printed p. 11–12 (PDF pp. 12–13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_GraphLaws

open Filter

namespace CoarseMatching.LowerBound

/-- Gillat Kol, STOC 2027 submission #1135 (October 2026), Lemma 4.1,
printed pp.11-12 / PDF pp.12-13. Both high-probability graph bounds AND the
next-page test consequence. The latter is uniform over all correct estimators.
No small-N assertion is made from an asymptotic assumption. -/
theorem lemma_4_1 (F : (N : ℕ) → GraphParameters N) (hF : Admissible F) :
    Tendsto (fun N => coverProbability N (F N)) atTop (nhds 1) ∧
    Tendsto (fun N => matchingProbability N (F N)) atTop (nhds 1) ∧
    ∀ᶠ N in atTop, ∀ (p S : ℕ) (A : Estimator (N+N) S) (mode : Arrival),
      1 ≤ p → Correct A mode p (F N).c true →
        1/4 ≤ graphTestGap (F N) A mode p := by sorry

end CoarseMatching.LowerBound
