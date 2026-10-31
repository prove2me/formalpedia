-- Prove2me | Theorems.Thm_FastCore_proposition_1_1
-- name    : FastCore.proposition_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:34:28.837612+00:00
-- url     : https://prove2.me/theorems/f18f1ca2-f67b-4f9a-8c82-de3e107dc630
-- title:
--   Proposition 1(1) (corrected: or $\bar\pi=1$ on $S_t$)
-- statement:
--   At each iteration $t$ of Algorithm 1 on a bid profile, with an oracle meeting Definition 6 and $\epsilon>0$:
--
--   1. $\pi^{(t)}$ is in the core;
--   2. for $t\ge1$, either $\bar\pi^{(t)}$ is outside the core or $\bar\pi^{(t)}_i=1$ for every $i\in S_t$.
--
--   In the second case all truncated bids of the bidders in $S_t$ vanish, so $T_t\cap S_t=\emptyset$ and the algorithm stops. This is why the printed theorem survives the correction.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - encoding: core vector indexed by N ∪ {0} satisfying (2) → `InCore`, on N only, with π₀ := w(N) − Σπᵢ, i.e. (3); reason: this is how the paper rewrites (2) as (3); no instance changes
--   - correction: "{π̄(t)} is outside of the core for t ≥ 1" → ¬InCore π̄(t), or π̄(t)ᵢ = 1 for every i ∈ S_t; reason: false as printed: at n = m = 1, b = 1, ε = 1/2 the run has π̄(1) = 1, a core point
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Proposition 1(1), p.18

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_Reachable

namespace FastCore

/-- Proposition 1(1) (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Proposition 1(1), p.18), corrected: at each iteration `π^(t)` is in
the core, and for `t ≥ 1`, `π̄^(t)` is outside the core or `π̄^(t)ᵢ = 1` on `S_t`.

**Formalization Note.** The printed clause "`π̄^(t)` is outside of the core" is false: at `n = m = 1`,
`b = 1`, `ε = 1/2` the run has `π̄^(1) = 1`, a core point. In the second case the truncated bids of
`S_t` vanish, so `T_t ∩ S_t = ∅`. -/
theorem proposition_1_1 {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {q : Oracle n} (hq : IsWinOrac b q)
    {ε : ℝ} (hε : 0 < ε)
    {c : Cfg n} (hc : Reachable q ε c) (hphase : c.phase = Phase.outer) :
    InCore b c.π ∧ (1 ≤ c.t → ¬ InCore b c.πbar ∨ ∀ i ∈ c.S, c.πbar i = 1) := by sorry

end FastCore
