-- Prove2me | Theorems.Thm_AdWordsMSVV_LowerBound_yao_step
-- name    : AdWordsMSVV.LowerBound.yao_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:30.252782+00:00
-- url     : https://prove2.me/theorems/cd6510ac-7b1f-42ae-8dbb-429cec64086b
-- title:
--   Proof of Theorem 9, p. 15 — Yao step: an average bound over the permuted instances bounds every randomized algorithm on some instance
-- statement:
--   Let $N, B$ be natural numbers, let $A$ be a randomized online algorithm for b-matching instances with $N$ bidders and $NB$ queries, and let $V$ be a real number. Let $I_\pi$ denote the permuted round instance with budget $B$ (round $Q_i$ is bid on by $\pi(i),\dots,\pi(N)$). If every deterministic online algorithm $a$ has average revenue at most $V$ over a uniformly random permutation,
--   $$\frac{1}{N!}\sum_{\pi}\mathrm{ALG}_a(I_\pi) \le V \quad\text{for all } a,$$
--   then there is a permutation $\pi$ with
--   $$\mathbb E_A[\mathrm{ALG}(I_\pi)] \le V.$$
--
--   This is the instance of Yao's principle that the proof of Theorem 9 invokes: it reduces the lower bound for randomized algorithms to an average-case bound for deterministic algorithms against the uniform distribution $\mathcal D$ on the permuted instances.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 15, proof of Theorem 9, first sentence

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace AdWordsMSVV.LowerBound

theorem yao_step (N B : ℕ) (A : RandAlg N (N * B)) (V : ℝ)
    (hV : ∀ a : DetAlg N (N * B),
      permAvg N (fun π => (revenue B (roundInstance N B π) a : ℝ)) ≤ V) :
    ∃ π : Equiv.Perm (Fin N), expectedRevenue B (roundInstance N B π) A ≤ V := by sorry

end AdWordsMSVV.LowerBound
