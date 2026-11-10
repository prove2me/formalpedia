-- Prove2me | Theorems.Thm_CoarseMatching_LowerBound_lemma_4_2
-- name    : CoarseMatching.LowerBound.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:37:41.172198+00:00
-- url     : https://prove2.me/theorems/88d7c40c-7e0c-41cc-be5f-c2ccdbe781f5
-- title:
--   Lemma 4.2 — Streaming to 2p+1-message Hidden-Core
-- statement:
--   For every admissible graph-parameter family with the same standing assumptions as Lemma 4.1, eventually every positive-pass estimator with $S\ge1$ satisfying Equation (1) on each legal simple bipartite stream gives a Hidden-Core protocol $\tau$ with
--
--   $$\mathrm{gap}(\tau)\ge\frac1{4N},\qquad r=2p+1,\qquad|M_j|\le S\ \ (1\le j\le r).$$
--
--   The messages alternate starting with Alice. The final output bit is sent and counted, and the output is determined by the transcript. Both edge arrival and vertex arrival are included. The eventual threshold is uniform over the estimator, its passes and its memory size.
--
--   This is the source’s operational streaming-to-communication simulation interface.
--
--   Differences from the source:
--   - encoding: a=o(N) and probability 1-o(1) → arbitrary eventually admissible parameter families with a(N)/N tending to zero, probability limits equal to one, and eventual conclusions; reason: standard family quantifiers give every source regime; no small-N consequence or fixed special family is asserted
--   - encoding: simple bipartite n-vertex graph streams with a known bipartition → Fin n labels, a supplied Boolean bipartition, and duplicate-free insertion or vertex lists; reason: every source graph and order has this labeling; correctness on duplicate-free streams also follows for algorithms supporting repeated insertions
--   - generalization: S-bit multipass streaming algorithms → input-local transition kernels with a free public pass index and arbitrary real output laws; reason: every ordinary algorithm embeds by charging retained data and random bits to the state; the public pass index is known in the source simulation
--   - encoding: protocols whose separate local input sizes are fixed → total strategies on all finite subsets with resource bounds on the size and promise domain; reason: invalid local inputs can be replaced by fixed valid local sets without communication; no valid input or resource guarantee is lost
--   - generalization: an estimator satisfying Equation (1) → correctness is needed only on the simple bipartite streams; reason: every stream used in the source simulation belongs to this class
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), Lemma 4.2, printed p. 13 (PDF p. 14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_GraphLaws

open Filter

namespace CoarseMatching.LowerBound

/-- Gillat Kol, STOC 2027 submission #1135 (October 2026), Lemma 4.2,
printed p.13 / PDF p.14. Exactly 2p+1 alternating messages, each at most S bits;
output bit actually sent and charged, transcript-determined output.
The eventual threshold is uniform over the estimator, p, S and arrival model. -/
theorem lemma_4_2 (F : (N : ℕ) → GraphParameters N) (hF : Admissible F) :
    ∀ᶠ N in atTop, ∀ (p S : ℕ) (A : Estimator (N+N) S) (mode : Arrival),
      1 ≤ p → 1 ≤ S → Correct A mode p (F N).c true →
      ∃ τ : Protocol (Finset (Fin N)) (Finset (Fin N)),
        τ.TranscriptDetermined ∧ OutputSentOn (HiddenInputs (F N).h (F N).d) τ ∧
        StartsWithOn (HiddenInputs (F N).h (F N).d) τ false ∧
        ProfileOn (HiddenInputs (F N).h (F N).d) τ (List.replicate (2*p+1) S) ∧
        1/(4*(N : ℝ)) ≤ hiddenGap (F N).h (F N).d (F N).P₀ (F N).P₁ τ := by sorry

end CoarseMatching.LowerBound
