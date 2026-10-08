-- Prove2me | Theorems.Thm_FZEchelon_Discounted_eq4_finite_decomposition
-- name    : FZEchelon.Discounted.eq4_finite_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:45:51.811617+00:00
-- url     : https://prove2.me/theorems/ad4e80ac-3b69-44fc-bd7c-0cbbf19d0915
-- title:
--   Eq. (4), p. 823 — Clark–Scarf decomposition $\hat g_n(\hat y, v^d, x^r) = \hat g_n^d(\hat y, v^d) + g_n^r(x^r)$
-- statement:
--   Consider the two-echelon inventory model of Federgruen and Zipkin under the standing assumptions of §1: positive cost factors $K, c^d, c^r, h^d, h^r, p^r$, a discount rate $0 \le \alpha \le 1$, and a nonnegative, continuous one-period demand $u$ with finite mean. For $n \ge 1$ let $x_n^{r*}$ be a critical number of the outlet program (2) for period $n$. Then for every $n \ge 0$ and every physical state, that is, outstanding orders $\hat y \ge 0$ and $x^r \le v^d$,
--   $$
--   \hat g_n(\hat y, v^d, x^r) = \hat g_n^d(\hat y, v^d) + g_n^r(x^r).
--   $$
--   Here $\hat g_n$ is the optimal $n$-period cost of the whole system (program (1)), $g_n^r$ that of the outlet alone (program (2)), and $\hat g_n^d$ that of the depot charged with the induced penalties $\hat P_n$ (program (3)).
--
--   This is the decomposition of Clark and Scarf in the event sequence of this paper. It reduces the multi-dimensional program (1) to two lower-dimensional programs, and it is the finite-horizon fact the infinite-horizon analysis builds on.
--
--   **Formalization Note.** The physical-state restriction ($\hat y \ge 0$, depot on-hand stock $v^d - x^r \ge 0$) is the domain on which the paper's state variables live, and it is preserved by every feasible action. The critical numbers enter as a sequence of minimizers; the paper's "let $x_n^{r*}$ denote the critical number" presumes they exist. The policy part of the paper's sentence after (4) is not included.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 823, eq. (4)

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Eq. (4), p. 823 (Clark–Scarf decomposition, finite horizon): on the physical states
(`ŷ ≥ 0`, `x^r ≤ v^d`), `ĝ_n(ŷ, v^d, x^r) = ĝ_n^d(ŷ, v^d) + g_n^r(x^r)` for every `n`, where
`x_n^{r*}` are the critical numbers of program (2). -/
theorem eq4_finite_decomposition (M : Model) (hM : M.StandingAssumptions)
    (xn : ℕ → ℝ) (hxn : M.IsCriticalNumberSeq xn)
    (n : ℕ) (s : M.State) (hs : M.InDomain s) :
    M.ghat n s = M.ghatd xn n (s.1, s.2.1) + M.gr n s.2.2 := by sorry

end FZEchelon.Discounted
