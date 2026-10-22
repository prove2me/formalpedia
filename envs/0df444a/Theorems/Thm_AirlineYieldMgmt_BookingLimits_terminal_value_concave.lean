-- Prove2me | Theorems.Thm_AirlineYieldMgmt_BookingLimits_terminal_value_concave
-- name    : AirlineYieldMgmt.BookingLimits.terminal_value_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T11:12:37.334986+00:00
-- url     : https://prove2.me/theorems/d6cddb7d-728a-403e-ad9b-c2e163570c77
-- title:
--   §1, p. 151 — the terminal value U₀(x) = E[−π(Y(x))] is concave and nonincreasing
-- statement:
--   In Model 1, let $0 \le \beta \le 1$ and let the overbooking penalty $\pi(y)$ be convex and nondecreasing in $y \ge 0$. Then the terminal value
--   $$U_0(x) \;=\; \mathrm{E}\big[-\pi(Y(x))\big],\qquad Y(x) \sim \mathrm{Bin}(x, 1-\beta),$$
--   is nonincreasing and concave in $x \in \{0,1,2,\dots\}$:
--   $$U_0(x+1) \le U_0(x) \quad\text{and}\quad U_0(x+2) - U_0(x+1) \;\le\; U_0(x+1) - U_0(x)\qquad\text{for all } x \ge 0.$$
--   This is the base case of the induction showing that every $U_n$ is concave and nonincreasing.
--
--   **Formalization Note.** Only the two hypotheses the sentence on the page invokes are assumed ($\pi$ convex and nondecreasing on $y \ge 0$), plus $0 \le \beta \le 1$; the other standing assumptions on $\pi$ (non-negativity, $\pi(y) = 0$ for $y \le C$) are not needed and are dropped, which makes the statement more general. The paper's Lemma 1 requires $0 < \gamma < 1$; here $\gamma = 1 - \beta$ may also be $0$ or $1$ (the boundary cases $U_0 \equiv -\pi(0)$ and $U_0(x) = -\pi(x)$). The conclusion is stated on all of $\mathbb N$, which contains the range $0 \le x \le N$ of Eq. (3).
-- source:
--   Subramanian, Stidham, Lautenbacher, Airline Yield Management with Overbooking, Cancellations, and No-Shows, Transp. Sci. 33(2), 1999, p. 151, §1, right column, first sentence after Lemma 1 (with Eq. (3), p. 150, and Eq. (6), p. 151)

import Mathlib
import Definitions.Def_AirlineYieldMgmt_BookingLimits_Model

namespace AirlineYieldMgmt.BookingLimits

/-- §1, p. 151, first sentence after Lemma 1: because `π` is convex and nondecreasing, the terminal
value `U_0(x) = E[-π(Y(x))]`, `Y(x) ∼ Bin(x, 1 - β)`, is nonincreasing and (discretely) concave
in `x`. -/
theorem terminal_value_concave {m : ℕ} (M : Model m)
    (hβ0 : 0 ≤ M.β) (hβ1 : M.β ≤ 1)
    (hπ_convex : ConvexOn ℝ (Set.Ici 0) M.π) (hπ_mono : MonotoneOn M.π (Set.Ici 0)) :
    Antitone (M.U 0) ∧
      ∀ x : ℕ, M.U 0 (x + 2) - M.U 0 (x + 1) ≤ M.U 0 (x + 1) - M.U 0 x := by sorry

end AirlineYieldMgmt.BookingLimits
