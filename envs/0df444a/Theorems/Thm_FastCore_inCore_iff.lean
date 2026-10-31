-- Prove2me | Theorems.Thm_FastCore_inCore_iff
-- name    : FastCore.inCore_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:32.812315+00:00
-- url     : https://prove2.me/theorems/ad06a3d8-e7cd-47ab-8692-5758a1a558a9
-- title:
--   Proof of Prop. 1(1) and p.14 — the core test
-- statement:
--   Let $\pi\ge0$. Then $\pi$ is in the core if and only if
--
--   $$
--   w(N)-\sum_{i\in N}\pi_i\ \ge\ w\bigl(N,\{\max(b_i(.)-\pi_i,0)\}\bigr).
--   $$
--
--   This makes line 5 of Procedure 2 an exact test of core membership with one oracle call, which is why the algorithm needs no explicit list of the exponentially many core constraints.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: core vector indexed by N ∪ {0} satisfying (2) → `InCore`, on N only, with π₀ := w(N) − Σπᵢ, i.e. (3); reason: this is how the paper rewrites (2) as (3); no instance changes
--   - generalization: the displays on pp.14 and 18, for the iterates π̲ and π(t) → an equivalence for every π ≥ 0; reason: the iterates are non-negative, so this specializes to the displays
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §3.2, p.14, and proof of Proposition 1, Part (1), p.18

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_w
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_InCore

namespace FastCore

/-- The core test (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §3.2, p.14, and proof of Proposition 1, Part (1), p.18): for `π ≥ 0`,
`π` is in the core iff `w(N) − ∑_N πᵢ ≥ w(N, {max(bᵢ(.) − πᵢ, 0)})`. This makes line 5 of
Procedure 2 a core test. -/
theorem inCore_iff {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : ∀ i, 0 ≤ π i) :
    InCore b π ↔ w (trunc b π) Finset.univ ≤ w b Finset.univ - ∑ i, π i := by sorry

end FastCore
