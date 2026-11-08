-- Prove2me | Theorems.Thm_CausalFailureRank_eq_4
-- name    : CausalFailureRank.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:02.347077+00:00
-- url     : https://prove2.me/theorems/2a0b097b-83ff-4c19-8124-93505828dc74
-- title:
--   Eq. (4) — ordered expression for $C(1,R)$, and positivity
-- statement:
--   For any initial remaining set $R$ of finite rank $d$,
--   $$C(1,R)=\sum_{i=1}^NA_i\,\mathbf 1\{b_i=d-1\},$$
--   where $b_i=0$ if $S_i\cap R=\emptyset$ and $b_i=\max_{r\in S_i\cap R}\rho(i+1,R\setminus\{r\})$ otherwise. Moreover $C(i,R)>0$ at every finite-rank state. Only the stages at which an erroneous write reduces the best continuation rank to $d-1$ contribute.
--
--   Differences from the source:
--   - encoding: $b_i=d-1$ → $b_i+1=d$ in the extended naturals; reason: avoids truncated subtraction; every rank is at least $1$, so they agree
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §3.1, eq. (4), p.6; App. B.3, p.17

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

open scoped Classical in
/-- **Eq. (4) and positivity.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Theorem 3.1, p.6, and App. B.3, p.17: "For (4), along the all-correct
path R stays fixed and ρ(i, R) is nondecreasing. The equality b_i = d − 1 forces ρ(i, R) = d, while
after the correct-path rank exceeds d no further term contributes at depth d. Expanding (2) along this
path proves the formula." and "Induction also proves positivity of every finite-rank coefficient."

**Formalization Note.** `b_i = d − 1` is `db + 1 = d` in `ℕ∞`: no truncated subtraction. Since every rank
is at least `1`, the two agree. -/
theorem eq_4 (I : Instance N q) :
    (∀ (R : Finset (Fin q)) (d : ℕ), rank I 0 R = d →
      C I 0 R = ∑ i : Fin N, if db I i R + 1 = d then A I i else 0) ∧
    ∀ (i : ℕ) (R : Finset (Fin q)) (d : ℕ), rank I i R = d → 0 < C I i R := by sorry

end CausalFailureRank
