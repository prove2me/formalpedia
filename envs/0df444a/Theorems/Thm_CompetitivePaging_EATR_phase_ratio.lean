-- Prove2me | Theorems.Thm_CompetitivePaging_EATR_phase_ratio
-- name    : CompetitivePaging.EATR.phase_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:16:32.656659+00:00
-- url     : https://prove2.me/theorems/268d8421-ef35-4d88-93cd-09fbb3b1d1c0
-- title:
--   Per phase, EATR's expected cost is at most $3/2$ times any lazy algorithm's amortized cost
-- statement:
--   Consider the uniform $2$-server problem on a metric space $M$ in which any two distinct points are at distance $1$, and algorithm EATR started with its servers on two distinct vertices $a,b$. Let $\sigma$ be a request sequence, let the requests with indices $i,\dots,i'-1$ form a complete EATR phase, and let $A$ be a lazy deterministic on-line algorithm with two servers. With $C_A$ the cost of $A$ on the requests of the phase and $d,d'$ the numbers of servers of $A$ not coinciding with EATR's servers at the beginning and at the end of the phase,
--   $$C_{\mathrm{EATR}}(\text{phase})\ \le\ \frac32\,\bigl(C_A+d-d'\bigr).$$
--
--   The quantity $C_A+d-d'$ is the amortized cost of $A$ for the phase, at least $l$; EATR's expected cost is $l+l/(l+1)$, and $(l+l/(l+1))/l=1+1/(l+1)\le 3/2$. Summed over the phases, the $d$ and $d'$ terms telescope, which yields Theorem 3.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 6, §4, proof of Theorem 3

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem phase_ratio {M : Type*} [MetricSpace M] [DecidableEq M]
    (hunif : ∀ x y : M, x ≠ y → dist x y = 1) (a b : M) (hab : a ≠ b)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    eatrPhaseCost a b σ i i'
      ≤ (3 / 2 : ℝ) * (algPhaseCost A σ i i' + (mismatch a b A σ i : ℝ)
          - (mismatch a b A σ i' : ℝ)) := by sorry

end CompetitivePaging.EATR
