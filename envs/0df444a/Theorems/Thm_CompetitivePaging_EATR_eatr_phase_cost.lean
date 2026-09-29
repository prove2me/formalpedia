-- Prove2me | Theorems.Thm_CompetitivePaging_EATR_eatr_phase_cost
-- name    : CompetitivePaging.EATR.eatr_phase_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:15:54.690365+00:00
-- url     : https://prove2.me/theorems/d101314f-f713-47d9-8044-aea012fd66ea
-- title:
--   The expected cost of a phase to EATR is $l + l/(l+1)$
-- statement:
--   Let algorithm EATR start with its servers on two distinct vertices $a,b$, let $\sigma$ be a request sequence, and let the requests with indices $i,\dots,i'-1$ form a complete EATR phase in which $l$ clean vertices are requested. Then the expected number of server moves EATR makes on the requests of the phase is exactly
--   $$l+\frac{l}{l+1}.$$
--
--   Each request to a clean vertex costs $1$, repeated requests to the most recently requested vertex cost nothing, and the terminating request costs the probability that the stale vertex requested is not covered. This is the on-line side of the per-phase comparison behind Theorem 3.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 6, §4, proof of Theorem 3

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem eatr_phase_cost {M : Type*} [DecidableEq M] (a b : M) (hab : a ≠ b)
    (σ : List M) (i i' : ℕ) (hph : IsCompletePhase a b σ i i') :
    eatrPhaseCost a b σ i i'
      = (numClean a b σ i i' : ℝ) + (numClean a b σ i i' : ℝ) / ((numClean a b σ i i' : ℝ) + 1) := by sorry

end CompetitivePaging.EATR
