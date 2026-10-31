-- Prove2me | Theorems.Thm_FastCore_proposition_1_3
-- name    : FastCore.proposition_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:34:51.565365+00:00
-- url     : https://prove2.me/theorems/bd075c18-62bc-4167-a845-f5c79376c36c
-- title:
--   Proposition 1(3) — $\mathcal G_{t+1}$ consists of $\epsilon$-tight constraints
-- statement:
--   Throughout a run of Algorithm 1, every set recorded so far is an $\epsilon$-tight core constraint with respect to the current core point. In particular, during iteration $t$, every set of $\mathcal G_{t+1}$ is an $\epsilon$-tight core constraint with respect to $\pi^{(t)}$.
--
--   At termination this is half of the certificate of correctness of the output.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - encoding: the collection G_(t+1) = {T₀,…,T_t} → the ghost list `c.log` in phase `search`; reason: it records the same sets, in order
--   - generalization: G_(t+1) with respect to π(t) → every recorded set with respect to the current point, at every reachable configuration; reason: phase `search` is the printed claim; the other phases follow it by persistence of tightness
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Proposition 1(3), p.19

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_IsEpsTight
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_Reachable

namespace FastCore

/-- Proposition 1(3) (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Proposition 1(3), p.19): every recorded set `T` is an `ε`-tight core
constraint for the current point. In phase `search` the record is `G_(t+1)` and the point is `π^(t)`,
which is the printed claim; in the other phases it is the same claim carried along by persistence. -/
theorem proposition_1_3 {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {q : Oracle n} (hq : IsWinOrac b q)
    {ε : ℝ} (hε : 0 < ε)
    {c : Cfg n} (hc : Reachable q ε c) {T : Finset (Fin n)} (hT : T ∈ c.log) :
    IsEpsTight b c.π ε T := by sorry

end FastCore
