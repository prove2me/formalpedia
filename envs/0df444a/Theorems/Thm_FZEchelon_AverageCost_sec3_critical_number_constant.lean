-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_sec3_critical_number_constant
-- name    : FZEchelon.AverageCost.sec3_critical_number_constant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:42:13.303628+00:00
-- url     : https://prove2.me/theorems/ca0b9671-a639-4903-8a6e-93c5c8930feb
-- title:
--   §3, p. 828 — with c^r = 0, x^{r*} is the critical number of every period and g^r_n(x) = nR(x^{r*}) for x ≤ x^{r*}
-- statement:
--   Let $\alpha = 1$ and $c^r = 0$, let $h^d, h^r, p^r > 0$, and let the demand be nonnegative, continuous and of finite mean. Let $x^{r*}$ be a global minimizer of $R$. Then for every $n \ge 1$:
--
--   1. $x^{r*}$ is a critical number for period $n$: it minimizes $G_n(w) = R(w) + E g^r_{n-1}(w - u)$;
--   2. $g^r_n(x) = n R(x^{r*})$ for every $x \le x^{r*}$.
--
--   So when shipments are free, the outlet's optimal policy is the same myopic critical-number policy in every period, and the outlet's finite-horizon cost below the critical number is $n$ times the one-period minimum.
--
--   **Formalization Note.** The paper writes $x^{r*}_n = x^{r*}$, which presumes the critical numbers are unique; the statement here says that $x^{r*}$ is a critical number for every period, which needs no choice of minimizer.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 828, §3, first paragraph ('A straightforward induction demonstrates that c^r = 0 implies ...')

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- §3, p. 828: with `α = 1` and `c^r = 0`, the critical number `x^{r*}` (a global minimizer of
`R`) is a critical number for every period `n ≥ 1`, and `g^r_n(x) = n R(x^{r*})` whenever
`x ≤ x^{r*}`. -/
theorem sec3_critical_number_constant (m : Model) (hα : m.α = 1) (hcr : m.cr = 0)
    (hhd : 0 < m.hd) (hhr : 0 < m.hr) (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xstar : ℝ) (hx : ∀ x, m.R xstar ≤ m.R x) :
    ∀ n : ℕ, 1 ≤ n →
      (∀ w, m.Gcrit n xstar ≤ m.Gcrit n w) ∧ ∀ x ≤ xstar, m.gr n x = n * m.R xstar := by sorry

end FZEchelon.AverageCost
