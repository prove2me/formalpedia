-- Prove2me | Theorems.Thm_CompetitivePaging_EATR_phase_stale_uniform
-- name    : CompetitivePaging.EATR.phase_stale_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:15:18.962658+00:00
-- url     : https://prove2.me/theorems/d8b741a6-cd35-4e6d-84f2-904962e7d304
-- title:
--   Before the terminating request there are $l+1$ stale vertices, each covered with probability $1/(l+1)$
-- statement:
--   Let algorithm EATR start with its servers on two distinct vertices $a,b$, let $\sigma$ be a request sequence, and let the requests with indices $i,\dots,i'-1$ form a complete EATR phase in which $l$ clean vertices are requested. Just before the request $\sigma(i'-1)$ to the stale vertex that terminates the phase:
--   1. the number of stale vertices is $l+1$;
--   2. every stale vertex $v$ is covered by a server of EATR with probability
--   $$\Pr[v \text{ is covered}] = \frac{1}{l+1}.$$
--
--   This is the probabilistic core of the analysis of EATR: it gives the expected cost of the terminating request, the only request of a phase whose cost is random.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 6, §4, proof of Theorem 3

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem phase_stale_uniform {M : Type*} [DecidableEq M] (a b : M) (hab : a ≠ b)
    (σ : List M) (i i' : ℕ) (hph : IsCompletePhase a b σ i i') :
    (stale (bookAfter a b (σ.take (i' - 1)))).card = numClean a b σ i i' + 1 ∧
      ∀ v ∈ stale (bookAfter a b (σ.take (i' - 1))),
        (lawAfter a b (σ.take (i' - 1))).toOuterMeasure {s | v ∈ servers s}
          = ((numClean a b σ i i' : ℝ≥0∞) + 1)⁻¹ := by sorry

end CompetitivePaging.EATR
