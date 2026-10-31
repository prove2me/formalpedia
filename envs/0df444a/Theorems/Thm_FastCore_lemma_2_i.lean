-- Prove2me | Theorems.Thm_FastCore_lemma_2_i
-- name    : FastCore.lemma_2_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:22.583984+00:00
-- url     : https://prove2.me/theorems/fd713b9c-2919-4fe3-b0c4-390aed3bdc9d
-- title:
--   Lemma 2, first bullet — truncated winners form a maximum binding constraint
-- statement:
--   Let $\{\pi_i\}_{i\in N}$ be non-negative utilities and $S\subseteq N$. If $S$ is the set of winning bidders of a maximum welfare allocation under the bids $\{\max(b_i(.)-\pi_i,0)\}_{i\in N}$ that allocates no set of zero value, then $S$ is a maximum binding core constraint for $\pi$:
--
--   $$
--   w(S')-\sum_{i\in S'}\pi_i\ \le\ w(S)-\sum_{i\in S}\pi_i\qquad\text{for all }S'\subseteq N.
--   $$
--
--   This is the exchange fact behind the algorithm: a single call to the winner determination oracle finds a most violated core constraint.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - reading: "Fix a vector of utilities" in Lemma 2 → π ≥ 0; reason: Definition 2 says non-negative utilities; for negative π the truncated empty bundle has positive value and the claim fails (one item, b₁ = b₂ = 1, π = (0, −1))
--   - reading: "the set of winning bidders for some maximum welfare allocation" in the first bullet → `IsZeroFreeWinnerSet`: an allocation with no zero-value bundle; reason: the proof on p.17 uses bᵢ(x′ᵢ) > πᵢ for winners, and the bullet is false for bare Definition 1 (one item, b = 1, π = 2)
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 2, first bullet, p.17

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsZeroFreeWinnerSet
import Definitions.Def_FastCore_IsMBCC

namespace FastCore

/-- Lemma 2, first bullet (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 2, p.17): for `π ≥ 0`, a set of winners of a maximum
welfare allocation under the truncated bids is a maximum binding constraint.

**Formalization Note.** "Winners" is `IsZeroFreeWinnerSet` and `π ≥ 0`: the proof on p.17 uses
`bᵢ(x'ᵢ) > πᵢ` for winners, and the bullet fails for bare Definition 1 (one item, `b = 1`, `π = 2`)
and for negative `π` (one item, `b₁ = b₂ = 1`, `π = (0, −1)`). -/
theorem lemma_2_i {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : ∀ i, 0 ≤ π i) {S : Finset (Fin n)} (hS : IsZeroFreeWinnerSet (trunc b π) S) :
    IsMBCC b π S := by sorry

end FastCore
