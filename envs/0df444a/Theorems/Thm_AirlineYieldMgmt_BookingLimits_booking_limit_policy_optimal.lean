-- Prove2me | Theorems.Thm_AirlineYieldMgmt_BookingLimits_booking_limit_policy_optimal
-- name    : AirlineYieldMgmt.BookingLimits.booking_limit_policy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:13:03.315544+00:00
-- url     : https://prove2.me/theorems/2e18c2c2-635b-44c9-8281-db4635e6ca74
-- title:
--   §1, Eq. (7), p. 151 — accepting a fare-class-i request at stage n is optimal iff the state is below the booking limit b_in
-- statement:
--   In Model 1 under its standing assumptions, fix a stage $1 \le n \le N$, a fare class $i$ and a reachable state $0 \le x \le N - n$. Let
--   $$b_{in} \;=\; \min\{x : U_{n-1}(x) - U_{n-1}(x+1) > r_{in}\}\qquad(b_{in} = \infty \text{ if there is no such } x)$$
--   be the booking limit of Eq. (7). Then accepting a class-$i$ request attains the maximum in the recursion (2), i.e.
--   $$r_{in} + U_{n-1}(x+1) \;\ge\; U_{n-1}(x),$$
--   if and only if $x < b_{in}$. So an optimal policy accepts a fare-class-$i$ request in state $x$ at stage $n$ exactly when $0 \le x < b_{in}$: optimal control is by booking limits that depend on the stage and the fare class. This is the paper's headline structural result.
--
--   **Formalization Note.** "An optimal policy accepts" is read as "the accept branch attains the maximum $\max\{r_{in} + U_{n-1}(x+1), U_{n-1}(x)\}$ in (2)"; $U_n$ is the function defined by the recursion, and no separate dynamic-programming optimality principle is stated. Ties are accepted ($\ge$), matching the strict inequality in (7). The minimum in (7) ranges over the reachable states $0 \le x \le N - n$ and is computed in `WithTop ℕ`, with `⊤` = $\infty$; $b_{in}$ is defined independently of the acceptance rule, so the content of the theorem is that the set of states where rejection is strictly better is an upper segment of the range. The standing assumptions include $q_n(0) = 0$ and non-negativity of $p_{0n}(x)$ on the reachable states only (see `Model`).
-- source:
--   Subramanian, Stidham, Lautenbacher, Airline Yield Management with Overbooking, Cancellations, and No-Shows, Transp. Sci. 33(2), 1999, p. 151, §1, Eq. (7) and the display after it

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model

namespace AirlineYieldMgmt.BookingLimits

/-- §1, Eq. (7) and the display after it, p. 151: under the standing assumptions of Model 1, at
every stage `1 ≤ n ≤ N`, for every fare class `i` and every reachable state `0 ≤ x ≤ N - n`,
accepting a class-`i` request attains the maximum in the recursion (2), i.e.
`r_{in} + U_{n-1}(x+1) ≥ U_{n-1}(x)`, if and only if `x < b_{in}`, where `b_{in}` is the booking
limit of Eq. (7). -/
theorem booking_limit_policy_optimal {m : ℕ} (M : Model m) (hM : M.Standing)
    (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ M.N) (i : Fin m) (x : ℕ) (hx : x ≤ M.N - n) :
    M.U (n - 1) x ≤ M.r n i + M.U (n - 1) (x + 1) ↔
      (x : WithTop ℕ) < M.bookingLimit n i := by sorry

end AirlineYieldMgmt.BookingLimits
