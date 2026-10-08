-- Prove2me | Theorems.Thm_FZEchelon_Discounted_iglehart_outlet_uniform
-- name    : FZEchelon.Discounted.iglehart_outlet_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:45:43.765191+00:00
-- url     : https://prove2.me/theorems/c87f9627-fe8c-484a-8130-0199d9dfe8d7
-- title:
--   §2, p. 825 (Iglehart) — $\beta_n = \sup_{x \le x^{r*}} |g_n^r(x) - g^r(x)|$ is finite for $n \ge 1$ and $\beta_n \to 0$
-- statement:
--   In the two-echelon model of Federgruen and Zipkin under the standing assumptions of §1, assume $\alpha < 1$ and the cost relation $\alpha^l p^r \ge (1-\alpha^l) h^d$. Let $x^{r*}$ be the critical number of the outlet problem (a global minimizer of $(1-\alpha)c^r x + R(x)$), let $x_n^{r*}$ ($n \ge 1$) be the critical numbers of the finite-horizon outlet program (2), and let $g^r$ be the pointwise limit of the outlet values $g_n^r$. Put
--   $$
--   \beta_n = \sup\{|g_n^r(x) - g^r(x)| : -\infty < x \le x^{r*}\}.
--   $$
--   Then $\beta_n < \infty$ for every $n \ge 1$, and
--   $$
--   \beta_n \to 0 \qquad (n \to \infty),
--   $$
--   i.e. $g_n^r \to g^r$ uniformly on $(-\infty, x^{r*}]$.
--
--   The paper quotes this from Iglehart (1963b). It is the input to Lemma 1: it controls the expectation terms in $\hat P_n - P$.
--
--   **Formalization Note.** The paper's sentence says "on the interval $(-\infty, x^{r*})$", but its definition of $\beta_n$ takes the supremum over $x \le x^{r*}$; the closed interval is used. Finiteness is claimed for $n \ge 1$ only: $g_0^r = 0$ while $g^r(x) = c^r(x^{r*} - x) + g^r(x^{r*})$ for $x \le x^{r*}$, so $\beta_0 = \infty$. The limit $g^r$ enters as a function together with the hypothesis that it is the pointwise limit; its existence is property (e). The cost relation is the condition the paper names in the proof of Theorem 1 (p. 827) and takes as standing for §2.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 825, §2, opening paragraph (Iglehart [1963b])

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- §2, p. 825 (Iglehart [1963b]): for `α < 1`, with `g^r` the pointwise limit of `g_n^r`, the
differences `g_n^r − g^r` are bounded on `(−∞, x^{r*}]` for every `n ≥ 1` (`β_n < ∞`) and converge
to `0` uniformly there (`β_n → 0`). -/
theorem iglehart_outlet_uniform (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (xn : ℕ → ℝ) (hxn : M.IsCriticalNumberSeq xn)
    (grInf : ℝ → ℝ) (hgr : ∀ x, Tendsto (fun n => M.gr n x) atTop (𝓝 (grInf x))) :
    (∀ n, 1 ≤ n → ∃ C : ℝ, ∀ x ≤ xstar, |M.gr n x - grInf x| ≤ C) ∧
      TendstoUniformlyOn M.gr grInf atTop (Set.Iic xstar) := by sorry

end FZEchelon.Discounted
