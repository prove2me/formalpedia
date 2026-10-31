-- Prove2me | Theorems.Thm_FastCore_proposition_1_2
-- name    : FastCore.proposition_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:34:28.272233+00:00
-- url     : https://prove2.me/theorems/c8633d40-7a79-4912-abef-3c671028c275
-- title:
--   Proposition 1(2) — $S_t$ is the intersection of $\mathcal G_t$, and it shrinks
-- statement:
--   At each iteration $t$ of Algorithm 1, with $\mathcal G_t=\{T_0,\dots,T_{t-1}\}$:
--
--   1. $S_t$ is the set of bidders that belong to every set of $\mathcal G_t$;
--   2. for $t\ge1$, the next set $T_t$ satisfies $S_t\setminus T_t\neq\emptyset$ and $T_t\notin\mathcal G_t$, so that $\mathcal G_t\ne\mathcal G_{t+1}$.
--
--   This strict progress is what bounds the number of iterations.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - encoding: the collection G_t = {T₀,…,T_(t−1)} → the ghost list `c.log`, of length t; reason: it records the same sets, in order
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Proposition 1(2), p.18

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_Reachable

namespace FastCore

/-- Proposition 1(2) (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Proposition 1(2), p.18): at each iteration `S_t` is the set of bidders
in all of `G_t = {T₀, …, T_(t−1)}` (the list `c.log`, of length `t`), and for `t ≥ 1`, the next set
`T_t` satisfies `S_t ∖ T_t ≠ ∅` and `T_t ∉ G_t`, so `G_t ≠ G_(t+1)`. -/
theorem proposition_1_2 {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {q : Oracle n} (hq : IsWinOrac b q)
    {ε : ℝ} (hε : 0 < ε)
    {c : Cfg n} (hc : Reachable q ε c) (hphase : c.phase = Phase.outer) :
    c.log.length = c.t ∧
      c.S = Finset.univ.filter (fun i => ∀ T ∈ c.log, i ∈ T) ∧
      (1 ≤ c.t → (c.S \ (q c.πbar).2).Nonempty ∧ (q c.πbar).2 ∉ c.log) := by sorry

end FastCore
