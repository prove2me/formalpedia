-- Prove2me | Theorems.Thm_CompetitivePaging_EATR_adversary_phase_bound
-- name    : CompetitivePaging.EATR.adversary_phase_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:14:49.398683+00:00
-- url     : https://prove2.me/theorems/8a901231-776b-4b4c-9a54-67345debb3ee
-- title:
--   In a complete EATR phase any lazy algorithm pays at least $l-d+d'$
-- statement:
--   Consider the uniform $2$-server problem on a metric space $M$ in which any two distinct points are at distance $1$, and algorithm EATR started with its servers on two distinct vertices $a,b$. Let $\sigma$ be a request sequence and let the requests with indices $i,\dots,i'-1$ form a complete EATR phase in which $l$ clean vertices are requested. Let $A$ be a lazy deterministic on-line algorithm with two servers. Let $d$ be the number of servers of $A$ that do not coincide with any of EATR's servers at the beginning of the phase, and $d'$ this number at the end of the phase. Then the cost $C_A$ incurred by $A$ on the requests of the phase satisfies
--   $$C_A\ \ge\ l-d+d'.$$
--
--   EATR phases have the structure singled out in the paper after the proof of Theorem 2: after the last request to a clean vertex, the other vertex used during the phase is requested. This is the lower bound on the adversary's cost that, summed over phases, makes the $d$ and $d'$ terms telescope, so that the amortized cost of any algorithm per phase is at least $l$.
--
--   **Formalization Note** EATR's servers at the beginning and at the end of a phase are deterministic (the set $P$ of the definition file), so $d$ and $d'$ are deterministic too. $A$ is a `KServer.OnlineAlgorithm 2 M`; laziness is the property `IsLazy` of the definition file.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 5, §3, paragraph after the proof of Theorem 2 (with d, d′ from p. 4), applied to EATR's phases as on p. 6, proof of Theorem 3

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_EATR_eatr

open scoped ENNReal

namespace CompetitivePaging.EATR

theorem adversary_phase_bound {M : Type*} [MetricSpace M] [DecidableEq M]
    (hunif : ∀ x y : M, x ≠ y → dist x y = 1) (a b : M) (hab : a ≠ b)
    (A : KServer.OnlineAlgorithm 2 M) (hA : IsLazy A) (σ : List M) (i i' : ℕ)
    (hph : IsCompletePhase a b σ i i') :
    (numClean a b σ i i' : ℝ) - (mismatch a b A σ i : ℝ) + (mismatch a b A σ i' : ℝ)
      ≤ algPhaseCost A σ i i' := by sorry

end CompetitivePaging.EATR
