-- Prove2me | Theorems.Thm_DualityStability_Stability_eq_4_6
-- name    : DualityStability.Stability.eq_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:58.275993+00:00
-- url     : https://prove2.me/theorems/466059b2-8be4-47e1-99d8-8a3ca1f997e7
-- title:
--   (4.6) — h(z) ≥ h(0) + h′(0; z) and h′(0; z) ≥ −h′(0; −z)
-- statement:
--   Let $F$ be a real vector space and $h : F \to [-\infty, +\infty]$ a convex function (convex epigraph) with $h(0)$ finite. Let $h'(0; z) = \lim_{\varepsilon \downarrow 0} [h(\varepsilon z) - h(0)]/\varepsilon$ be its directional derivative (4.3). Then for every $z \in F$,
--
--   $$
--   h(z) \ge h(0) + h'(0; z), \qquad h'(0; z) \ge -h'(0; -z).
--   $$
--
--   These two elementary facts about directional derivatives of a convex function turn an upper bound on $h$ near $0$ into a lower bound on $h'(0; \cdot)$ near $0$, which is the stability part of Theorem 1.
--
--   **Formalization Note** Both inequalities are in `EReal`. The paper states (4.6) for "a convex function" and applies it to $h = \inf (P(\cdot))$; the statement here is the general one for any convex $h$ finite at $0$. The right-hand side $-h'(0; -z)$ is a negation, so no undefined form $(+\infty) - (+\infty)$ arises; $h(0) + h'(0;z)$ is a sum of a finite number and an extended real.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 176, (4.6), proof of Theorem 1

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_StablySet

namespace DualityStability.Stability

/-- Rockafellar (1967), (4.6), p. 176: two elementary facts about the directional derivatives of a
convex function `h : F → [−∞, +∞]` with `h(0)` finite:
`h(z) ≥ h(0) + h′(0; z)` and `h′(0; z) ≥ −h′(0; −z)` for all `z`. -/
theorem eq_4_6 {F : Type*} [AddCommGroup F] [Module ℝ F] (h : F → EReal) (hconv : ConvexFn h)
    (h0_bot : h 0 ≠ ⊥) (h0_top : h 0 ≠ ⊤) :
    ∀ z : F, h 0 + dirDeriv0 h z ≤ h z ∧ -dirDeriv0 h (-z) ≤ dirDeriv0 h z := by sorry

end DualityStability.Stability
