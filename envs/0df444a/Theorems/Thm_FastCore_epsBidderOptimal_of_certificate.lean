-- Prove2me | Theorems.Thm_FastCore_epsBidderOptimal_of_certificate
-- name    : FastCore.epsBidderOptimal_of_certificate
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:32:02.816861+00:00
-- url     : https://prove2.me/theorems/5bf758e4-24b7-417a-a5e6-932d38d7368a
-- title:
--   Proof of Theorem 1 — the certificate step
-- statement:
--   Let $\pi$ be a core point and let $\mathcal T$ be a finite family of $\epsilon$-tight core constraints with respect to $\pi$ such that every bidder $j$ is missing from some $T\in\mathcal T$. Then $\pi$ is $\epsilon$-bidder optimal.
--
--   Raising a coordinate $j$ by more than $\epsilon$ violates an $\epsilon$-tight constraint not containing $j$.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: core vector indexed by N ∪ {0} satisfying (2) → `InCore`, on N only, with π₀ := w(N) − Σπᵢ, i.e. (3); reason: this is how the paper rewrites (2) as (3); no instance changes
--   - generalization: the output π(T) and the collection G_(T+1) → any core point and any finite family with empty intersection; reason: the output and G_(T+1) are such a pair, so this specializes to the printed step
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, pp.19–20

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsEpsBidderOptimal
import Definitions.Def_FastCore_IsEpsTight

namespace FastCore

/-- The certificate step (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, pp.19–20): a core point with a family of
`ε`-tight core constraints with empty intersection is `ε`-bidder optimal. -/
theorem epsBidderOptimal_of_certificate {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b)
    {π : Fin n → ℝ} {ε : ℝ} {Ts : List (Finset (Fin n))} (hcore : InCore b π)
    (htight : ∀ T ∈ Ts, IsEpsTight b π ε T) (hempty : ∀ j, ∃ T ∈ Ts, j ∉ T) :
    IsEpsBidderOptimal b ε π := by sorry

end FastCore
