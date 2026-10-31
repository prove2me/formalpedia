-- Prove2me | Theorems.Thm_FastCore_core_le_marginal
-- name    : FastCore.core_le_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:04.579457+00:00
-- url     : https://prove2.me/theorems/0e2457f2-4096-4c07-bd41-fb9a4251afb9
-- title:
--   Proof of Lemma 1 — $\pi_i\le w(N)-w(N\setminus\{i\})\le b_i(x^*_i)$
-- statement:
--   Let $\{\pi_i\}_{i\in N}$ be a core point and $\{x^*_i\}_{i\in N}$ a maximum welfare allocation. Then for every bidder $i$,
--
--   $$
--   \pi_i\ \le\ w(N)-w(N\setminus\{i\})\ \le\ b_i(x^*_i).
--   $$
--
--   In particular every core utility is at most $1$. This gives the non-negativity of the payments in Lemma 1, and it controls the case of Proposition 1 in which $\bar\pi$ remains in the core.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: core vector indexed by N ∪ {0} satisfying (2) → `InCore`, on N only, with π₀ := w(N) − Σπᵢ, i.e. (3); reason: this is how the paper rewrites (2) as (3); no instance changes
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Lemma 1, p.12

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsWelfareMaximizing

namespace FastCore

/-- The display in the proof of Lemma 1 (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Lemma 1, p.12):
`πᵢ ≤ w(N) − w(N ∖ {i}) ≤ bᵢ(x*ᵢ)`. -/
theorem core_le_marginal {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : InCore b π) {x : Fin n → Finset (Fin m)} (hx : IsWelfareMaximizing b x) (i : Fin n) :
    π i ≤ w b Finset.univ - w b (Finset.univ.erase i) ∧
      w b Finset.univ - w b (Finset.univ.erase i) ≤ b i (x i) := by sorry

end FastCore
