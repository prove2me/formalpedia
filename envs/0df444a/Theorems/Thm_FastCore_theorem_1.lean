-- Prove2me | Theorems.Thm_FastCore_theorem_1
-- name    : FastCore.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:33:07.811898+00:00
-- url     : https://prove2.me/theorems/899cb17a-eec6-463f-a29a-aa2f0cbcd981
-- title:
--   Theorem 1 — water-filling returns an $\epsilon$-bidder optimal core point fast
-- statement:
--   There are absolute constants $C_1,C_2>0$ such that the following holds for all $n,m$, every bid profile $\{b_i\}$ on $n$ bidders and $m$ items, every oracle meeting the specification of WIN-ORAC for these bids, and every $\epsilon>0$. Algorithm 1 halts, and at the return:
--
--   1. its output $\pi$ is an $\epsilon$-bidder optimal core point;
--   2. it has made at most $(n+1)+n\lceil\log_2(n/\epsilon)\rceil_+$ oracle calls;
--   3. it has spent additional time at most $n\bigl((2n+1)+n\lceil\log_2(n/\epsilon)\rceil_+\bigr)$;
--   4. if $n\ge1$ and $\epsilon\le n/2$, the oracle calls are at most $C_1\,n\log(n/\epsilon)$ and the additional time at most $C_2\,n^2\log(n/\epsilon)$.
--
--   This gives a deterministic combinatorial algorithm for an $\epsilon$-bidder optimal core point with $O(n\log(n/\epsilon))$ evaluations of a winner determination oracle, although the core has exponentially many constraints.
--
--   Differences from the source:
--   - encoding: bidders N = {1,…,n} and bundles in 2^[m] → `Fin n` and `Finset (Fin m)`, with n = 0 and m = 0 allowed; reason: Lean convention; the same instances
--   - encoding: black-box oracle, with "any set in W(·)" on line 4 → a function `q` of the truncation, universally quantified, with the specification required at π ≥ 0 only; reason: the run queries only π ≥ 0, and the algorithm has no other access to the bids
--   - reading: `return π(t)` typeset at while-body level on line 11 → π(t) is returned exactly when S_(t+1) = ∅, the else branch of line 6; reason: a return after one pass contradicts Figure 1, p.15 ("Once all bidders are frozen") and p.19 (S_(T+1) = ∅)
--   - reading: "does not allocate sets of zero value" (p.10), for the auction allocation rule → applied to truncated bids as well: the oracle returns a zero-free winner set; reason: the proof of Lemma 2 needs it, and under bare Definition 1 the algorithm need not halt
--   - encoding: core vector indexed by N ∪ {0} satisfying (2) → `InCore`, on N only, with π₀ := w(N) − Σπᵢ, i.e. (3); reason: this is how the paper rewrites (2) as (3); no instance changes
--   - reading: O(n log(n/ϵ)) and O(n² log(n/ϵ)) → explicit bounds for all n and ε > 0, plus absolute constants C₁, C₂, chosen before the instance, for n ≥ 1 and ε ≤ n/2; reason: the printed bound is at most 0 at ε ≥ n although the algorithm makes at least one call; both forms are kept
--   - reading: "an additional time" → the counter `ticks` with unit-cost operations: n per pass, n per bisection step, n per Core-Search exit; reason: the paper counts only "extra additions" informally; this count dominates its |S| per bisection step
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Theorem 1, p.19

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_IsEpsBidderOptimal
import Definitions.Def_FastCore_IsWinOrac
import Definitions.Def_FastCore_run
import Definitions.Def_FastCore_bisectionSteps

namespace FastCore

/-- Theorem 1 (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Theorem 1, p.19): Algorithm 1 halts and returns an `ε`-bidder optimal core
point, with `O(n log(n/ε))` oracle calls and additional time `O(n² log(n/ε))`.

**Formalization Note.** The bounds are stated twice: explicitly for every `n` and `ε > 0`, and with
absolute constants `C₁`, `C₂`, chosen before the instance, for `n ≥ 1` and `ε ≤ n/2`, where
`log(n/ε) > 0`. The printed bound is not positive at `ε ≥ n`, although the algorithm makes at least
one call for `n ≥ 1`. The oracle is any `q` meeting `IsWinOrac`, and `step` has no access to `b`. -/
theorem theorem_1 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n m : ℕ) (b : Bids n m), IsBidProfile b → ∀ q : Oracle n, IsWinOrac b q →
        ∀ ε : ℝ, 0 < ε →
          ∃ K : ℕ,
            let c := run q ε K
            c.phase = Phase.done ∧
            IsEpsBidderOptimal b ε c.π ∧
            c.calls ≤ (n + 1) + n * bisectionSteps n ε ∧
            c.ticks ≤ n * ((2 * n + 1) + n * bisectionSteps n ε) ∧
            (1 ≤ n → ε ≤ (n : ℝ) / 2 →
              (c.calls : ℝ) ≤ C₁ * n * Real.log ((n : ℝ) / ε) ∧
              (c.ticks : ℝ) ≤ C₂ * n ^ 2 * Real.log ((n : ℝ) / ε)) := by sorry

end FastCore
