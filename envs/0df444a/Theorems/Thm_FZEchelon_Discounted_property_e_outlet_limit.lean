-- Prove2me | Theorems.Thm_FZEchelon_Discounted_property_e_outlet_limit
-- name    : FZEchelon.Discounted.property_e_outlet_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:06.106031+00:00
-- url     : https://prove2.me/theorems/8a2c5025-b844-4832-adf4-215237be0351
-- title:
--   Property (e), p. 824 — for $\alpha < 1$, $g_n^r \to g^r = B^{r\alpha}$ and $g^r$ has slope $-c^r$ below $x^{r*}$
-- statement:
--   In the two-echelon model of Federgruen and Zipkin under the standing assumptions of §1, suppose the discount rate satisfies $\alpha < 1$, and let $x^{r*}$ be a global minimizer of $(1-\alpha)c^r x + R(x)$, the critical number of the outlet problem. Then there is a function $g^r : \mathbb R \to \mathbb R$ such that:
--
--   1. the finite-horizon outlet values converge, $g_n^r(x) \to g^r(x)$ for every $x$;
--   2. $g^r$ is the optimal discounted cost of the outlet problem $IH^r_\alpha$: for every $x$, $g^r(x) = B^{r\alpha}(x) = \inf_{\pi^r} B^{r\alpha}(x \mid \pi^r)$, the infimum over admissible shipment policies, which are constrained only by $z \ge 0$;
--   3. $g^r(x) = c^r(x^{r*} - x) + g^r(x^{r*})$ for every $x \le x^{r*}$.
--
--   This is one of the well-known facts about the single-location outlet problem that the paper quotes (from Heyman and Sobel). The limit $g^r$ is the outlet half of the limit function $g = g^d + g^r$ used in Lemmas 3 and 4.
--
--   **Formalization Note.** The optimal outlet cost is an extended real; item 2 states that it is finite and equal to $g^r$. Admissible policies are measurable, non-anticipative, deterministic history-dependent shipment rules with $z \ge 0$ along every demand path.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 824, property (e)

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Property (e), p. 824: for `α < 1` the outlet values `g_n^r` converge to a function `g^r`, which is
the optimal discounted cost `B^{rα}` of the outlet problem `IH_α^r`, and
`g^r(x) = c^r (x^{r*} − x) + g^r(x^{r*})` for `x ≤ x^{r*}`. -/
theorem property_e_outlet_limit (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar) :
    ∃ grInf : ℝ → ℝ,
      (∀ x, Tendsto (fun n => M.gr n x) atTop (𝓝 (grInf x))) ∧
      (∀ x, ((grInf x : ℝ) : EReal) =
        ⨅ (π : Policy ℝ) (_ : M.outletSystem.Admissible π x), M.outletSystem.discCost M.α M.ν π x) ∧
      (∀ x ≤ xstar, grInf x = M.cr * (xstar - x) + grInf xstar) := by sorry

end FZEchelon.Discounted
