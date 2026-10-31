-- Prove2me | Theorems.Thm_FastCore_oracle_calls_le
-- name    : FastCore.oracle_calls_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:09.3339+00:00
-- url     : https://prove2.me/theorems/5ab9d261-ca1a-4b25-9e2a-9bd977c5954e
-- title:
--   Proof of Theorem 1 — oracle calls (corrected: $n+1$ passes, ceiling)
-- statement:
--   At every point of a run of Algorithm 1, the number of oracle calls so far is at most
--
--   $$
--   (n+1)+\sum_{t=1}^{n}\lceil\log_2(t/\epsilon)\rceil_+.
--   $$
--
--   There are at most $n+1$ passes through line 4, and at most $n$ runs of Core-Search; the $k$-th runs on at most $n-k+1$ bidders, and a run on $S$ makes $\lceil\log_2(|S|/\epsilon)\rceil_+$ calls.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - correction: Total # of oracle calls ≤ n + Σ_(t=0)^T log(|S_(t+1)|/ϵ) ≤ n + Σ_(t=1)^n log(t/ϵ) → (n + 1) + Σ_(t=1)^n ⌈log₂(t/ε)⌉₊; reason: false as printed: at n = m = 1, b = 1, ε = 1 the run makes 2 calls and the right side is 1; the passes can be n + 1 and the logarithm needs a ceiling. The bound O(n log(n/ε)) of Theorem 1 is unaffected
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, p.20

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_Reachable
import Definitions.Def_FastCore_bisectionSteps

namespace FastCore

/-- The oracle-call count (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, p.20), corrected: every configuration of a
run has made at most `(n + 1) + ∑_{t=1}^n ⌈log₂(t/ε)⌉₊` oracle calls.

**Formalization Note.** The printed `n + ∑_t log(|S_(t+1)|/ε)` fails at `n = m = 1`, `b = 1`,
`ε = 1` (two calls, right side `1`): lines 3–5 run up to `n + 1` times, and the logarithm needs a
ceiling. The sum over `t = 1, …, n` is the paper's middle bound `n + ∑_{t=1}^n log(t/ε)` with
these two corrections: the `k`-th Core-Search runs on at most `n − k + 1` bidders and makes
`⌈log₂(|S|/ε)⌉₊` calls. The bound `O(n log(n/ε))` of Theorem 1 is unaffected. -/
theorem oracle_calls_le {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {q : Oracle n} (hq : IsWinOrac b q)
    {ε : ℝ} (hε : 0 < ε)
    {c : Cfg n} (hc : Reachable q ε c) :
    c.calls ≤ (n + 1) + ∑ t ∈ Finset.Icc 1 n, bisectionSteps t ε := by sorry

end FastCore
