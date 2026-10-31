-- Prove2me | Theorems.Thm_FastCore_ticks_le
-- name    : FastCore.ticks_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:34:01.794037+00:00
-- url     : https://prove2.me/theorems/f92de0bd-8ea7-482e-98e0-0e4ab43d1c0d
-- title:
--   Proof of Theorem 1 — additional time
-- statement:
--   At every point of a run of Algorithm 1, the additional time so far is at most
--
--   $$
--   n\Bigl((2n+1)+\sum_{t=1}^{n}\lceil\log_2(t/\epsilon)\rceil_+\Bigr).
--   $$
--
--   Here additional time is the work outside the oracle: $n$ unit operations for each pass through lines 3–5, each bisection step and each exit from Core-Search.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - reading: "extra additions" / "Extra time needed ≤ Σ_(t=0)^T |S_(t+1)| log(|S_(t+1)|/ϵ)" → the counter `ticks` with unit-cost operations: n per pass, n per bisection step, n per Core-Search exit, bounded by n((2n + 1) + Σ_(t=1)^n ⌈log₂(t/ε)⌉₊); reason: the paper leaves the cost model informal; this count dominates its |S_(t+1)| per bisection step, so it implies a bound at least as strong as the printed O(n² log(n/ε))
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, p.20

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_Reachable
import Definitions.Def_FastCore_bisectionSteps

namespace FastCore

/-- The additional-time count (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, proof of Theorem 1, p.20): every configuration of a run has
spent at most `n ((2n + 1) + ∑_{t=1}^n ⌈log₂(t/ε)⌉₊)` additional time, the paper's
`∑_{t=1}^n t log(t/ε)` in the cost model of `ticks`.

**Formalization Note.** `ticks` charges `n` per pass of lines 3–5, per bisection step and per exit
from Core-Search. This dominates the paper's count of `|S_(t+1)|` additions per bisection step. -/
theorem ticks_le {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {q : Oracle n} (hq : IsWinOrac b q)
    {ε : ℝ} (hε : 0 < ε)
    {c : Cfg n} (hc : Reachable q ε c) :
    c.ticks ≤ n * ((2 * n + 1) + ∑ t ∈ Finset.Icc 1 n, bisectionSteps t ε) := by sorry

end FastCore
