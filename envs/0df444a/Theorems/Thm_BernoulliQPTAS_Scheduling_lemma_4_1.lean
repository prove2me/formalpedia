-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_4_1
-- name    : BernoulliQPTAS.Scheduling.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:48.226219+00:00
-- url     : https://prove2.me/theorems/dd58566e-5d02-4e3b-8b95-770dcc0cef98
-- title:
--   Lemma 4.1 — properties of the reuse rule
-- statement:
--   For any positive rational size $p$ and integer $K\ge1$, define $g_p=p/K$, $\gamma=1+1/K$, and $R_p(s)=g_p(\lceil s/g_p\rceil+K)$. Then, for every $s\ge0$,
--
--   $$s+p\le R_p(s)<s+\gamma p,\qquad R_p(s)\in g_p\mathbb Z.$$
--
--   In addition, $R_p$ is nondecreasing on the nonnegative half-line. These properties constrain machine reservations, while actual completion remains at $s+p$.
--
--   Differences from the source:
--   - encoding: positive job sizes, integer K at least one, and nonnegative start times → rational p, natural K with 1 ≤ K, and an explicit monotonicity domain Set.Ici 0; reason: the rational size domain is the standing model on p.6 and the real-time domain is unchanged
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 4.1, p. 10; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_4_1 (p : ℚ) (hp : 0 < p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ s : ℝ, 0 ≤ s → s + p ≤ reuseReal p K s ∧
      reuseReal p K s < s + (1 + 1 / (K : ℝ)) * p) ∧
    MonotoneOn (reuseReal p K) (Set.Ici 0) ∧
    (∀ s : ℝ, 0 ≤ s → ∃ z : ℤ, reuseReal p K s = (z : ℝ) * (p / K)) := by sorry

end BernoulliQPTAS.Scheduling
