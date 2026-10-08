-- Prove2me | Theorems.Thm_FZEchelon_AverageCost_property_f_outlet_average
-- name    : FZEchelon.AverageCost.property_f_outlet_average
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:41:58.845507+00:00
-- url     : https://prove2.me/theorems/1bb8ae50-a08f-4053-b15f-b624629e3259
-- title:
--   Property (f), p. 824 — for α = 1, g^r_n(x)/n → B^r(x) = a^r = c^r μ + R(x^{r*}) for all x
-- statement:
--   Consider the outlet problem alone, without discounting ($\alpha = 1$): the state is the outlet's inventory position $x$, the action is a shipment $z \ge 0$, the one-period cost is $c^r z + R(x + z)$, and the position moves to $x + z - u$. Let $g^r_n$ be the minimal expected $n$-period cost of program (2), and $B^r(x)$ the minimal average cost over measurable policies from the initial position $x$. Let $x^{r*}$ be the critical number, a global minimizer of $R$. Assume all six cost factors are positive and the demand is nonnegative, continuous (no atoms) and has a finite mean $\mu$. Then for every $x$,
--   $$\lim_{n \to \infty} \frac{1}{n} g^r_n(x) = B^r(x) = a^r = c^r \mu + R(x^{r*}).$$
--
--   In words: value iteration for the outlet problem converges, after division by the horizon, to the minimal average cost, which does not depend on the initial position. In §3 this identifies the outlet's share $a^r$ of the system's average cost.
--
--   **Formalization Note.** With $\alpha = 1$, property (b) of p. 824 says that $x^{r*}$ is the global minimum of $(1 - \alpha)c^r x + R(x) = R(x)$, which is the hypothesis on $x^{r*}$. The limit is a real limit; $B^r(x)$ is an infimum in the extended reals, and the statement says it equals the real number $c^r\mu + R(x^{r*})$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 824, §1, property (f)

import Mathlib
import Definitions.Def_FZEchelon_AverageCost_Model
import Definitions.Def_FZEchelon_AverageCost_Policies
import Definitions.Def_FZEchelon_AverageCost_ValueFunctions
open MeasureTheory Filter Topology

namespace FZEchelon.AverageCost

/-- Property (f), §1, p. 824: for `α = 1`, `lim_{n→∞} (1/n) g^r_n(x) = B^r(x) = a^r = c^r μ + R(x^{r*})`
for all `x`, where `x^{r*}` is the critical number (property (b) with `α = 1`: a global minimizer
of `R`). -/
theorem property_f_outlet_average (m : Model) (hα : m.α = 1)
    (hK : 0 < m.K) (hcd : 0 < m.cd) (hcr : 0 < m.cr) (hhd : 0 < m.hd) (hhr : 0 < m.hr)
    (hpr : 0 < m.pr)
    [IsProbabilityMeasure m.ν] (hν0 : m.ν (Set.Iio 0) = 0) (hνatom : ∀ t, m.ν {t} = 0)
    (hνint : Integrable id m.ν)
    (xstar : ℝ) (hx : ∀ x, m.R xstar ≤ m.R x) :
    ∀ x : ℝ, Tendsto (fun n : ℕ => m.gr n x / n) atTop (𝓝 (m.cr * m.μ + m.R xstar)) ∧
      m.outletOptAvg x = ((m.cr * m.μ + m.R xstar : ℝ) : EReal) := by sorry

end FZEchelon.AverageCost
