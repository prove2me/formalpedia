-- Prove2me | Theorems.Thm_FasterSFM_theorem_1
-- name    : FasterSFM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:33.390193+00:00
-- url     : https://prove2.me/theorems/8e9e5c61-d758-40d4-a945-f0379ffd283f
-- title:
--   Theorem 1 — w.h.p. an exact minimizer with $O(n^2\log n)$ oracle calls and $O(n^3\log^{O(1)}n)$ arithmetic
-- statement:
--   Let $h:2^U\to\mathbb R$ be a submodular function on a ground set of size $n$, accessible only through a value oracle, and let $EO$ bound the time of one oracle call. There is a randomized algorithm in exact real arithmetic that, with high probability, returns an exact minimizer of $h$ using $O(n^2\log n)$ value-oracle calls and total running time
--
--   $$O(n^2\log n\cdot EO+n^3\log^{O(1)}n).$$
--
--   Formally: for every $c>0$ there are one admissible program $P$ of the randomized exact-arithmetic value-oracle RAM and constants $C>0$, $k\in\mathbb N$ such that for every $n\ge1$ and every submodular $h:2^{\{0,\dots,n-1\}}\to\mathbb R$, with probability at least
--
--   $$1-(n+2)^{-c}$$
--
--   over the fair-coin tape, the run of $P$ halts with an output $X$ satisfying $h(X)\le h(Y)$ for all $Y$, after at most $Cn^2\log(n+2)$ value queries and at most $Cn^3(\log(n+2))^k$ executed instructions. Since the total running time is (queries)$\cdot EO$ + (instructions), this is the theorem's time bound.
--
--   The result improves the best strongly polynomial bounds for submodular minimization, $O(n^3\log n\cdot EO+n^4\log n)$, by a factor of about $n$ in both the number of oracle calls and the arithmetic.
--
--   Differences from the source:
--   - reading: O(n² log n) and O(n³ log^{O(1)} n) → explicit constants C > 0 and k ∈ ℕ, chosen after c and before n and h, with log(n + 2) for log n; reason: reading R1: Theorem 27's log(n + 2); log 1 = 0 would forbid even the endpoint queries at n = 1
--   - reading: a ground set of size n → U = Fin n with n ≥ 1; reason: reading R1: at n = 0 the instruction bound C·0 would forbid halting
--   - reading: "with high probability" → for every c > 0, failure probability at most (n + 2)^{−c}, over the coins, for each fixed h; reason: reading R2: Remark 29's boosting supports every polynomial; (n+2)^{−c} avoids the vacuous n^{−c} at n = 1
--   - reading: a randomized algorithm in exact real arithmetic → one finite admissible program of the randomized exact-arithmetic value-oracle RAM: rational literals, + − × ÷, √, integer pointers, one-bit bitmaps, fair coins; no exp, log, floor; reason: readings R3–R4: the weakest machine on which the algorithm runs, which gives the strongest theorem
--   - encoding: total running time O(n² log n EO + n³ log^{O(1)} n) → two counters on the same run: queries ≤ C n² log(n+2) and executed instructions ≤ C n³ (log(n+2))^k; reason: reading R5: total time = queries · EO + instructions, so the two bounds are the time bound
--   - encoding: returns an exact minimizer with high probability → a measurable set of tapes of the stated probability on which the run halts with a minimizer and both bounds hold at that step; reason: reading R6: one success event; a measurable subset avoids outer measure
--   - encoding: h : 2^U → ℝ submodular → h : Finset (Fin n) → ℝ with NonmonotoneSubmod.Shared.Submodular h; reason: same condition (p.3); nothing else is assumed
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Theorem 1, p.2; restated as Theorem 27, p.44

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_FasterSFM_Machine

namespace FasterSFM

/-- **Theorem 1** (p.2), restated as **Theorem 27** (p.44).

Ene & Nguyen, *A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization*,
arXiv:2610.25403v1, Theorem 1, p.2; Theorem 27, p.44.

"Let h be a submodular function on a ground set of size n represented via a function value oracle.
Let EO be an upper bound on the running time of a single call to the value oracle. There is a
randomized algorithm that, with high probability, returns an exact minimizer of h using O(n² log n)
value oracle calls and total running time O(n² log n EO + n³ log^{O(1)} n)."

For every `c > 0` there are one admissible program `P` of the randomized exact-arithmetic value-oracle
RAM and constants `C > 0`, `k ∈ ℕ` such that for every `n ≥ 1` and every submodular
`h : 2^{Fin n} → ℝ`, a measurable set of coin tapes of probability at least `1 − (n+2)^{−c}` lies in
the success event: the run halts with an exact minimizer of `h`, after at most `C n² log(n+2)` value
queries and at most `C n³ (log(n+2))^k` executed instructions.

**Formalization Note.**
* R1: `O(·)` is an explicit `C` and `log^{O(1)}` an explicit power `k`, both chosen after `c` and
  before `n` and `h`; `log n` is read as `log(n+2)` (Theorem 27); `n ≥ 1`.
* R2: "with high probability" is: for every `c > 0`, failure probability at most `(n+2)^{−c}`, for
  every fixed `h` (worst case over inputs, probability over the coins only).
* R3–R4: the machine of `FasterSFM.Machine` (exact real `+ − × ÷` with `x/0 = 0`, `√` with
  `√(negative) = 0`, rational literals, integer pointers, one-bit bitmaps, fair coins).
* R5: total running time is `queries · EO + work`; the theorem bounds both counters on the same run,
  so the paper's `O(n² log n · EO + n³ log^{O(1)} n)` follows by definition.
* R6: halting, exactness and both bounds hold on one measurable event. -/
theorem theorem_1 :
    ∀ c : ℝ, 0 < c →
      ∃ (P : Program) (_ : Admissible P) (C : ℝ) (k : ℕ), 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ (h : Finset (Fin n) → ℝ), NonmonotoneSubmod.Shared.Submodular h →
          ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ E ⊆ {ω | Success P n h C k ω} ∧
            1 - ((n : ℝ) + 2) ^ (-c) ≤ (coinTape E).toReal := by sorry

end FasterSFM
