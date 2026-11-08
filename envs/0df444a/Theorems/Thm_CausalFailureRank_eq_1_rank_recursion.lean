-- Prove2me | Theorems.Thm_CausalFailureRank_eq_1_rank_recursion
-- name    : CausalFailureRank.eq_1_rank_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:09.567378+00:00
-- url     : https://prove2.me/theorems/934fb8d9-41c6-401b-932a-449d3a952d61
-- title:
--   Eq. (1) — rank recursion and game characterization
-- statement:
--   For a fixed instance, $\rho(i,R)>k$ if and only if some causal allocator handles every pattern of at most $k$ errors from stage $i$ on, and $\rho(i,R)=\infty$ at healthy termination. For every stage,
--   $$\rho(i,R)=\min\{d_g,\,1+d_b\},\qquad d_g=\rho(i+1,R),\qquad d_b\le d_g.$$
--   This makes the game's rank computable by backward induction, and is what the coefficient recursion runs on.
--
--   Differences from the source:
--   - encoding: rank via an adaptive error adversary → existence of a causal allocator handling all patterns of at most $k$ errors; reason: for a pure causal strategy the adversary can simulate it; §2 notes pure strategies suffice
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, p.5; §3.1, eq. (1), p.6

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **Eq. (1), and the game characterization.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, p.5; §3.1, p.6. "ρ(i, R) > k means that some
allocator handles every adaptive pattern of at most k future errors. Healthy termination has rank
∞." and "ρ(i, R) = min{d_g, 1 + d_b}. More remaining tools can only help, so d_g ≥ d_b."

**Formalization Note.** Rank is defined by the game; here (1) is a theorem. 0-based stages. -/
theorem eq_1_rank_recursion (I : Instance N q) :
    (∀ (i : ℕ) (R : Finset (Fin q)) (k : ℕ), (k : ℕ∞) < rank I i R ↔ Handles I.S i R k) ∧
    (∀ (i : ℕ) (R : Finset (Fin q)), N ≤ i → rank I i R = ⊤) ∧
    ∀ (i : Fin N) (R : Finset (Fin q)),
      rank I i.val R = min (rank I (i.val + 1) R) (1 + db I i R) ∧
      db I i R ≤ rank I (i.val + 1) R := by sorry

end CausalFailureRank
