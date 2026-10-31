-- Prove2me | Theorems.Thm_FastCore_epsTight_mono
-- name    : FastCore.epsTight_mono
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:32:02.237267+00:00
-- url     : https://prove2.me/theorems/43b20565-888b-4ef9-bfe3-283af13932fd
-- title:
--   Proof of Prop. 1(3) — $\epsilon$-tightness persists
-- statement:
--   Suppose $T$ is an $\epsilon$-tight core constraint with respect to $\pi$, and let $\pi'$ be a core point with $\pi'_i\ge\pi_i$ for every $i$. Then $T$ is an $\epsilon$-tight core constraint with respect to $\pi'$.
--
--   This is why constraints stay in the certificate as the utilities rise.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: core vector indexed by N ∪ {0} satisfying (2) → `InCore`, on N only, with π₀ := w(N) − Σπᵢ, i.e. (3); reason: this is how the paper rewrites (2) as (3); no instance changes
--   - generalization: successive iterates π(t−1), π(t) of the algorithm → any π and any core point π′ ≥ π; reason: the iterates are non-decreasing and π(t) is in the core, so this specializes to the printed claim
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Proposition 1, Part (3), p.19

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsEpsTight

namespace FastCore

/-- `ε`-tightness persists (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Proposition 1, Part (3), p.19): if `T` is `ε`-tight for
`π`, and `π' ≥ π` is in the core, then `T` is `ε`-tight for `π'`. -/
theorem epsTight_mono {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π π' : Fin n → ℝ}
    {ε : ℝ} {T : Finset (Fin n)} (hcore : InCore b π') (hle : ∀ i, π i ≤ π' i)
    (hT : IsEpsTight b π ε T) : IsEpsTight b π' ε T := by sorry

end FastCore
