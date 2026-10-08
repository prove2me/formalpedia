-- Prove2me | Theorems.Thm_CachonCoord_TwoLocation_eq_38
-- name    : CachonCoord.TwoLocation.eq_38
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:55:50.24095+00:00
-- url     : https://prove2.me/theorems/c009fbb2-1077-404a-bac1-8d8612abf9e1
-- title:
--   Eq. (38), p. 83 — ∫ c′(s̄ − x) f_s(x) dx = 0 has a unique root, ⇔ Pr(D_r + D_s ≤ s̄) = β/(h_r + β); optima with s_s ≤ 0 have s_r + s_s = s̄
-- statement:
--   In the two-location base-stock model, with $c'(y) = (h_r + \beta)F_r(y) - \beta$:
--   1. there is exactly one $\bar s$ with
--   $$\int_0^\infty c'(\bar s - x)\,f_s(x)\,dx = 0; \qquad (38)$$
--   2. for every $s$, the equation $\int_0^\infty c'(s-x)f_s(x)\,dx = 0$ holds if and only if
--   $$\Pr(D_r + D_s \le s) = \frac{\beta}{h_r+\beta},$$
--   where $D_r$ and $D_s$ are independent;
--   3. every optimal policy $\{\tilde s^2_r, \tilde s^2_s\}$ (a minimizer of $\Pi$ over $\mathbb R^2$) with $\tilde s^2_s \le 0$ satisfies $\tilde s^2_r + \tilde s^2_s = \bar s$.
--
--   This describes the candidate optimal policies in which the supplier holds no inventory: only the total base stock $\bar s$ matters. Comparing $\bar s$ with $\tilde s^1_r$ decides which kind of policy is optimal.
--
--   **Formalization Note** The integral over $[0,\infty)$ is written over $\mathbb R$ against the law of $D_s$; the two agree because $D_s \ge 0$. The independence of $D_r$ and $D_s$ is implicit on the page; it enters only through $\Pr(D_r + D_s \le s)$, which is formalized as the convolution of the two laws evaluated on $(-\infty, s]$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.8.4, p. 83, Eq. (38) with the preceding sentence on candidate policies with s_s ≤ 0 and the display Pr(D_r + D_s ≤ s̄) = β/(h_r + β)

import Mathlib
import Definitions.Def_CachonCoord_TwoLocation_Model

open MeasureTheory

namespace CachonCoord.TwoLocation

/-- §6.8.4, p. 83, Eq. (38). The equation `∫_0^∞ c'(s̄ − x) f_s(x) dx = 0` has exactly one
solution `s̄`; it is equivalent to `Pr(D_r + D_s ≤ s̄) = β/(h_r + β)` for independent `D_r`,
`D_s` (the law of `D_r + D_s` being the convolution of the two laws); and every optimal policy
`{s̃²_r, s̃²_s}` with `s̃²_s ≤ 0` satisfies `s̃²_r + s̃²_s = s̄`. -/
theorem eq_38 (M : Model) :
    (∃! sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0) ∧
    (∀ s : ℝ, ∫ x, M.cDeriv (s - x) ∂M.lawS = 0 ↔
      (M.lawR.conv M.lawS).real (Set.Iic s) = M.beta / (M.hr + M.beta)) ∧
    (∀ sbar : ℝ, ∫ x, M.cDeriv (sbar - x) ∂M.lawS = 0 →
      ∀ sr ss : ℝ, IsMinOn (fun p : ℝ × ℝ => M.Pi p.1 p.2) Set.univ (sr, ss) → ss ≤ 0 →
        sr + ss = sbar) := by sorry

end CachonCoord.TwoLocation
