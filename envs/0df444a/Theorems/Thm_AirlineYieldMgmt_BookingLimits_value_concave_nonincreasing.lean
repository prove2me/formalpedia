-- Prove2me | Theorems.Thm_AirlineYieldMgmt_BookingLimits_value_concave_nonincreasing
-- name    : AirlineYieldMgmt.BookingLimits.value_concave_nonincreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:12:48.559853+00:00
-- url     : https://prove2.me/theorems/605adbea-34cf-4dcd-a322-be1f1eb0f527
-- title:
--   §1, p. 151 — every value function Uₙ is nonincreasing and concave on the reachable states 0 ≤ x ≤ N − n
-- statement:
--   In Model 1 under its standing assumptions, for every stage $0 \le n \le N$ the value function $U_n$ of recursion (2)–(3) is nonincreasing and concave on the reachable states $\{0, 1, \dots, N-n\}$:
--   $$U_n(x+1) \le U_n(x)\quad\text{whenever } x + 1 \le N - n,$$
--   $$U_n(x) - U_n(x+1) \;\le\; U_n(x+1) - U_n(x+2)\quad\text{whenever } x + 2 \le N - n.$$
--   Equivalently, the opportunity cost $U_n(x) - U_n(x+1)$ of accepting a booking is non-negative and nondecreasing in $x = 0, 1, \dots, N - n - 1$. This is the structural property from which the optimality of booking limits follows.
--
--   **Formalization Note.** The standing assumptions are those of `Model.Standing`, including the two conventions the page leaves implicit: $q_n(0) = 0$, and non-negativity of the null-event probability $p_{0n}(x) = 1 - \sum_i p_{in} - q_n(x)$ only for $1 \le n \le N$ and $0 \le x \le N - n$. Both claims are restricted to the reachable range, where the paper states them; $U_n$ is defined on all of $\mathbb N$ but no claim is made outside the range. Concavity and monotonicity are discrete (differences on $\mathbb N$).
-- source:
--   Subramanian, Stidham, Lautenbacher, Airline Yield Management with Overbooking, Cancellations, and No-Shows, Transp. Sci. 33(2), 1999, p. 151, §1, right column, second sentence after Lemma 1 (cf. Lippman and Stidham 1977, Theorem 1)

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model

namespace AirlineYieldMgmt.BookingLimits

/-- §1, p. 151 (cf. Lippman–Stidham 1977, Theorem 1): under the standing assumptions of Model 1,
for every stage `0 ≤ n ≤ N`, `U_n(·)` is nonincreasing and concave on the reachable states
`0 ≤ x ≤ N - n`, so that `U_n(x) - U_n(x+1)` is nondecreasing in `x = 0, 1, …, N - n - 1`. -/
theorem value_concave_nonincreasing {m : ℕ} (M : Model m) (hM : M.Standing)
    (n : ℕ) (hn : n ≤ M.N) :
    (∀ x : ℕ, x + 1 ≤ M.N - n → M.U n (x + 1) ≤ M.U n x) ∧
      (∀ x : ℕ, x + 2 ≤ M.N - n →
        M.U n x - M.U n (x + 1) ≤ M.U n (x + 1) - M.U n (x + 2)) := by sorry

end AirlineYieldMgmt.BookingLimits
