-- Prove2me | Theorems.Thm_FastCore_truncWelfare_eq
-- name    : FastCore.truncWelfare_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:50.33129+00:00
-- url     : https://prove2.me/theorems/a03d6b51-9976-4c6f-a9b9-0d1be13776e1
-- title:
--   Eq. (5) — truncated welfare equals the most binding constraint
-- statement:
--   Let $\pi\ge0$. Every coalition satisfies
--
--   $$
--   w(S)-\sum_{i\in S}\pi_i\ \le\ w\bigl(N,\{\max(b_i(.)-\pi_i,0)\}\bigr),
--   $$
--
--   and equality holds whenever $S$ is the set of winners of a maximum welfare allocation under the truncated bids that allocates no set of zero value.
--
--   So the oracle's value is exactly $\max_{S\subseteq N}\bigl(w(S)-\sum_{i\in S}\pi_i\bigr)$.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - reading: "Fix a vector of utilities" in Lemma 2 → π ≥ 0; reason: Definition 2 says non-negative utilities; for negative π the truncated empty bundle has positive value and the claim fails (one item, b₁ = b₂ = 1, π = (0, −1))
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Lemma 2, eq. (5), p.17, as used on p.18

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_w
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsZeroFreeWinnerSet

namespace FastCore

/-- The chain (5) (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Lemma 2, eq. (5), p.17, as used on p.18): for `π ≥ 0`, the max
welfare under truncated bids is `max_S (w(S) − ∑_S πᵢ)`, attained at every zero-free winner set of
the truncated bids. -/
theorem truncWelfare_eq {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : ∀ i, 0 ≤ π i) :
    (∀ S, IsZeroFreeWinnerSet (trunc b π) S →
        w (trunc b π) Finset.univ = w b S - ∑ i ∈ S, π i) ∧
      ∀ S, w b S - ∑ i ∈ S, π i ≤ w (trunc b π) Finset.univ := by sorry

end FastCore
