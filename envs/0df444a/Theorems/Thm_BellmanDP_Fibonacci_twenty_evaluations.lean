-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_twenty_evaluations
-- name    : BellmanDP.Fibonacci.twenty_evaluations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:43:56.786745+00:00
-- url     : https://prove2.me/theorems/c2784b35-0a33-4301-b9de-2ae11c5e91bd
-- title:
--   Chapter I, Eq. (22.4) — $F_{20} > 10{,}000$: twenty evaluations locate the maximum within $10^{-4} L$
-- statement:
--   With $F_0 = F_1 = 1$ and $F_n = F_{n-1} + F_{n-2}$,
--   $$F_{20} > 10{,}000 ,$$
--   and consequently, for every interval $[0, L]$ with $L > 0$, there is a deterministic adaptive procedure that, for every function $f$ strictly unimodal on $[0, L]$, evaluates $f$ at most $20$ times and announces an interval of length at most $10^{-4} L$ containing the maximizer of $f$.
--
--   This is Bellman's practical reading of Theorem 11: the precision of Fibonacci search grows geometrically with the number of evaluations.
--
--   **Formalization Note** "Within $10^{-4}$ of the original interval length" is read as an announced interval of length at most $10^{-4} L$. $F_{20} = 10946$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, Eq. (22.4) and the sentence following it, p. 36

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, after Eq. (22.4), p. 36: `F₂₀ > 10,000`; hence the maximum of a strictly
unimodal function on an interval of any length `L > 0` can always be located within `10⁻⁴ L` with
at most 20 calculations of the value of the function. -/
theorem twenty_evaluations :
    10000 < bookFib 20 ∧
    ∀ L : ℝ, 0 < L → ∃ T : SearchTree ℝ (ℝ × ℝ), Locates T L (L / 10 ^ 4) 20 := by sorry

end BellmanDP.Fibonacci
