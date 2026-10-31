-- Prove2me | Theorems.Thm_FastCore_lemma_1
-- name    : FastCore.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:31:25.728312+00:00
-- url     : https://prove2.me/theorems/55a2fff4-e06b-4171-a6d9-392681c112e3
-- title:
--   Lemma 1 — a core point and an optimal allocation give a core outcome
-- statement:
--   Let $\{b_i\}$ be a bid profile, let $\{\pi_i\}_{i\in N}$ be a core point, and let $\{x^*_i\}_{i\in N}$ be any maximum welfare allocation. Set
--
--   $$
--   p^*_i=b_i(x^*_i)-\pi_i\qquad(i\in N).
--   $$
--
--   Then the outcome $\{(x^*_i,p^*_i)\}_{i\in N}$ is in the core.
--
--   This is what connects core points in utility space to payments, and it justifies searching for core points without fixing the allocation.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: core vector indexed by N ∪ {0} satisfying (2) → `InCore`, on N only, with π₀ := w(N) − Σπᵢ, i.e. (3); reason: this is how the paper rewrites (2) as (3); no instance changes
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 1, p.11

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsWelfareMaximizing
import Definitions.Def_FastCore_OutcomeInCore

namespace FastCore

/-- Lemma 1 (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 1, p.11): a core point `π` and a maximum welfare allocation `x*` give the
core outcome `(x*, p*)` with `p*ᵢ = bᵢ(x*ᵢ) − πᵢ`. -/
theorem lemma_1 {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : InCore b π) {x : Fin n → Finset (Fin m)} (hx : IsWelfareMaximizing b x) :
    OutcomeInCore b x (fun i => b i (x i) - π i) := by sorry

end FastCore
