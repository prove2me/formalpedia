-- Prove2me | Theorems.Thm_FastCore_lemma_3
-- name    : FastCore.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:33:03.507183+00:00
-- url     : https://prove2.me/theorems/52bb333e-d6e8-40a7-a23e-9623a707f50e
-- title:
--   Lemma 3 — at most $n$ iterations
-- statement:
--   For a bid profile, an oracle meeting Definition 6 and $\epsilon>0$, Algorithm 1 terminates in at most $|N|=n$ iterations: its run reaches the return with $t\le n$.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - reading: "at most |N| = n iterations" → the counter t, i.e. the runs of Core-Search, is at most n at the return; reason: the passes through line 4 can be n + 1 (n = m = 1, b = 1), and they are counted in the call bound
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 3, p.19

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_run

namespace FastCore

/-- Lemma 3 (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Lemma 3, p.19): Algorithm 1 terminates in at most `|N| = n` iterations.

**Formalization Note.** Iterations are increments of `t`, that is, runs of Core-Search. The passes
through line 4 can be `n + 1`; they are counted in `oracle_calls_le`. -/
theorem lemma_3 {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {q : Oracle n} (hq : IsWinOrac b q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K, (run q ε K).phase = Phase.done ∧ (run q ε K).t ≤ n := by sorry

end FastCore
