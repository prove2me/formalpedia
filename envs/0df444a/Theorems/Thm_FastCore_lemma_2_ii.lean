-- Prove2me | Theorems.Thm_FastCore_lemma_2_ii
-- name    : FastCore.lemma_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:28.724017+00:00
-- url     : https://prove2.me/theorems/413e4fcd-cbe8-46e5-bcef-fd39993877c2
-- title:
--   Lemma 2, second bullet — the converse when $\pi>0$ on $S$
-- statement:
--   Let $\{\pi_i\}_{i\in N}$ be a vector of utilities and $S\subseteq N$ with $\pi_i>0$ for all $i\in S$. If $S$ is a maximum binding core constraint for $\pi$, then $S$ is the set of winning bidders of some maximum welfare allocation under the bids $\{\max(b_i(.)-\pi_i,0)\}_{i\in N}$.
--
--   Together with the first bullet, this characterizes the most binding constraints as winner sets of truncated bids.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - reading: "the set of winning bidders for some maximum welfare allocation" in the second bullet → `IsWinnerSet`: the literal Definition 1, with zero-value bundles allowed; reason: the bullet is false for zero-free winner sets (n = m = 1, b = 1, π = 1); the optimal allocation x^S built on p.17 may have zero truncated value
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 2, second bullet, p.17

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsWinnerSet
import Definitions.Def_FastCore_IsMBCC

namespace FastCore

/-- Lemma 2, second bullet (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 2, p.17): if `πᵢ > 0` on `S`, a maximum
binding constraint `S` is the set of winners of a maximum welfare allocation under the truncated
bids.

**Formalization Note.** "Winners" is the literal Definition 1 (`IsWinnerSet`): the bullet fails for
`IsZeroFreeWinnerSet` (`n = m = 1`, `b = 1`, `π = 1`). -/
theorem lemma_2_ii {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, 0 < π i) (hM : IsMBCC b π S) :
    IsWinnerSet (trunc b π) S := by sorry

end FastCore
