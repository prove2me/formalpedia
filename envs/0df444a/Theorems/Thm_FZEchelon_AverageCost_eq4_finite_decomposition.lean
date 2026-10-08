-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_eq4_finite_decomposition
-- name    : FZEchelon.AverageCost.eq4_finite_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:42:02.8592+00:00
-- url     : https://prove2.me/theorems/f15107a7-a9f9-40f3-87ce-6a5cd1f91cc6
-- title:
--   Eq. (4), p. 823 — Clark–Scarf decomposition ĝ_n = ĝ^d_n + g^r_n of the finite-horizon program
-- statement:
--   Let $0 \le \alpha \le 1$, let $K, h^d, h^r, p^r > 0$ and $c^d, c^r \ge 0$, with $\alpha^l p^r \ge (1 - \alpha^l)h^d$, and let the demand be nonnegative, continuous and of finite mean. Let $x^{r*}_n$ ($n \ge 1$) be critical numbers of the outlet program (2), i.e. global minimizers of $G_n(w) = c^r w + R(w) + \alpha E g^r_{n-1}(w - u)$, and build the induced penalties $\hat P_n$ and the depot program (3) from them. Then for every $n \ge 0$ and every physical state ($\tilde y \ge 0$, $x^r \le v^d$),
--   $$\hat g_n(\tilde y, v^d, x^r) = \hat g^d_n(\tilde y, v^d) + g^r_n(x^r).$$
--
--   This is the result of Clark and Scarf: the system's finite-horizon program splits into an outlet program and a depot program in which the outlet's shortfalls are charged through the induced penalties. It is the finite-horizon fact on which the infinite-horizon analysis rests.
--
--   **Formalization Note.** The condition $\alpha^l p^r \ge (1 - \alpha^l)h^d$ is not on p. 823; the paper assumes only that the costs "are related in certain ways ... that preclude it being optimal never to order" (p. 821), and names this condition in the proof of Theorem 1 (p. 827). It keeps the one-period costs bounded below on the constraint set, and holds automatically for $\alpha = 1$. The paper assumes all six costs positive (p. 821) and §3 sets $c^d = c^r = 0$; the statement allows $c^d, c^r \ge 0$ and so covers both. The physical-state restriction ($\tilde y \ge 0$, $x^r \le v^d$) is the paper's implicit state space. The decomposition does not depend on which minimizer is chosen as $x^{r*}_n$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 823, eq. (4); cost relation from p. 827 (proof of Theorem 1)

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- Eq. (4), §1, p. 823 (Clark and Scarf): `ĝ_n(ŷ, v^d, x^r) = ĝ^d_n(ŷ, v^d) + g^r_n(x^r)` for every
`n` and every physical state, where `P̂_n` in (3) is built from critical numbers `x_n^{r*}`
(global minimizers of `G_n`). Stated for `0 ≤ α ≤ 1`. -/
theorem eq4_finite_decomposition (m : Model) (hα0 : 0 ≤ m.α) (hα1 : m.α ≤ 1)
    (hK : 0 < m.K) (hcd : 0 ≤ m.cd) (hcr : 0 ≤ m.cr) (hhd : 0 < m.hd) (hhr : 0 < m.hr)
    (hpr : 0 < m.pr) (hrel : (1 - m.α ^ m.l) * m.hd ≤ m.α ^ m.l * m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xn : ℕ → ℝ) (hxn : ∀ n, 1 ≤ n → ∀ w, m.Gcrit n (xn n) ≤ m.Gcrit n w) :
    ∀ (n : ℕ) (s : SysState m.L), InDomain s →
      m.ghat n s = m.ghatd xn n (s.1, s.2.1) + m.gr n s.2.2 := by sorry

end FZEchelon.AverageCost
