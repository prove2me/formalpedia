-- Prove2me | Theorems.Thm_FastCore_coreSearch_exit
-- name    : FastCore.coreSearch_exit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:34:23.431183+00:00
-- url     : https://prove2.me/theorems/5374c502-e632-4c90-b4e2-0354b423e184
-- title:
--   Core-Search guarantee (corrected: $\bar\pi$ may be the untested endpoint $\Delta_h=1$)
-- statement:
--   Consider a run of Algorithm 1 with precision $\epsilon>0$ at the moment Core-Search exits, with current core point $\pi$, active set $S$ and endpoints $\Delta_l,\Delta_h$. Let $\underline\pi$ and $\bar\pi$ be $\pi$ raised on $S$ by $\Delta_l$ and $\Delta_h$. Then
--
--   $$
--   w(N)-\sum_{i\in N}\underline\pi_i\ \ge\ w\bigl(N,\{\max(b_i(.)-\underline\pi_i,0)\}\bigr),
--   $$
--
--   $$
--   w(N)-\sum_{i\in N}\bar\pi_i\ <\ w\bigl(N,\{\max(b_i(.)-\bar\pi_i,0)\}\bigr)\quad\text{or}\quad \Delta_h=1,
--   $$
--
--   $$
--   \sum_{i\in N}\bar\pi_i-\sum_{i\in N}\underline\pi_i\ \le\ \epsilon.
--   $$
--
--   So the search brackets the boundary of the core in $\ell_1$ distance $\epsilon$, except that the initial endpoint $\Delta_h=1$ is never tested.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - correction: π̄ satisfies w(N) − Σπ̄ᵢ < w(N, truncated), always → that inequality, or Δh = 1; reason: false as printed: Procedure 2 never tests Δh = 1, and at n = m = 1, b = 1, ε = 1/2 it exits with π̄ = 1, which is in the core
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §3.2, displays, p.14

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_w
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_bump
import Definitions.Def_FastCore_Reachable

namespace FastCore

/-- The Core-Search guarantee (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §3.2, displays, p.14), corrected: when the search exits, `π̲`
is in the core, `π̄` is outside the core or `Δh` is the untested endpoint `1`, and
`∑ π̄ᵢ − ∑ π̲ᵢ ≤ ε`.

**Formalization Note.** The printed second display is false: Procedure 2 never tests `Δh = 1`, and
at `n = m = 1`, `b = 1`, `ε = 1/2` it exits with `π̄ = 1`, a core point. -/
theorem coreSearch_exit {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {q : Oracle n} (hq : IsWinOrac b q)
    {ε : ℝ} (hε : 0 < ε)
    {c : Cfg n} (hc : Reachable q ε c) (hphase : c.phase = Phase.search)
    (hexit : c.Δh - c.Δl ≤ ε / (c.S.card : ℝ)) :
    w (trunc b (bump c.π c.S c.Δl)) Finset.univ ≤
        w b Finset.univ - ∑ i, bump c.π c.S c.Δl i ∧
      (w b Finset.univ - ∑ i, bump c.π c.S c.Δh i <
          w (trunc b (bump c.π c.S c.Δh)) Finset.univ ∨ c.Δh = 1) ∧
      ∑ i, bump c.π c.S c.Δh i - ∑ i, bump c.π c.S c.Δl i ≤ ε := by sorry

end FastCore
