-- Prove2me | Theorems.Thm_DevContest_eq_EC_40_ic
-- name    : DevContest.eq_EC_40_ic
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:50:41.831762+00:00
-- url     : https://prove2.me/theorems/5f7b7cae-b34f-4a62-9d23-6c282d3b7c66
-- title:
--   Displays (EC.39)–(EC.40) — full effort attains the first-stage value iff $V_1-V_0\ge c/\lambda$
-- statement:
--   Let $\lambda,c>0$. Let $V_1$ be bounded and measurable on $[0,\infty)$, and let $p,x_1,x_0,\phi$ be effort paths. Let $V_{0,t}$ be the value of the problem (EC.39) from $t$, that is, the supremum of the objective over all effort paths. Then full effort attains this value from every date if and only if
--   $$
--   V_{1,t}-V_{0,t}\ge\frac c\lambda\qquad\text{for almost every }t\ge0.
--   $$
--   This is the incentive-compatibility constraint of an agent with no success.
--
--   **Formalization Note** $V_0$ is the supremum, as in (EC.39), not the payoff of full effort: the equivalence fails for the latter, because it does not exclude a negative value.
--
--   Differences from the source:
--   - encoding: the HJB equation at a belief $p$, with a pointwise condition → the equivalence for the integral problem, with the condition at almost every date; reason: the data are only measurable, so a condition on $V_1$ can hold only almost everywhere; the HJB equation is a route to this equivalence
--   - generalization: the rival at the equilibrium strategy under PCSD → arbitrary measurable belief, rival efforts and disclosure probability, and bounded measurable $V_1$; reason: the page's data are one instance
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, displays (EC.39)–(EC.40), p.ec17

import Mathlib
import Definitions.Def_DevContest_firstStageObjective

open MeasureTheory

namespace DevContest

/-- The first-stage incentive constraint, displays (EC.39)–(EC.40), Khorasani, Körpeoğlu, Krishnan,
*Dynamic Development Contests*, author manuscript, p.ec17. Let `V0 t` be the value (the supremum over
efforts) of the problem (EC.39), for a bounded measurable continuation payoff `V1`, belief `p`, rival
efforts `x1`, `x0` and disclosure probability `φ`. Then full effort attains the value from every date
if and only if `V1 - V0 ≥ c/λ` at almost every date.

**Formalization Note.** `V0` is the value, not the payoff of full effort: with the latter the
equivalence fails, since `V1 - V0 = c/λ` also holds when the payoff of full effort is negative.
The HJB equation of p.ec17 is replaced by this statement, so the efforts may be merely measurable. -/
theorem eq_EC_40_ic {lam c : ℝ} (hlam : 0 < lam) (hc : 0 < c) {V1 p x1 x0 φ V0 : ℝ → ℝ}
    (hV1 : Measurable V1) (hV1b : ∃ B, ∀ t, 0 ≤ t → |V1 t| ≤ B)
    (hp : IsEffort p) (hx1 : IsEffort x1) (hx0 : IsEffort x0) (hφ : IsEffort φ)
    (hV0 : ∀ t, 0 ≤ t →
      IsLUB {v | ∃ x, IsEffort x ∧ v = firstStageObjective lam c V1 p x1 x0 φ x t} (V0 t)) :
    (∀ t, 0 ≤ t → firstStageObjective lam c V1 p x1 x0 φ (fun _ => 1) t = V0 t) ↔
      ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), c / lam ≤ V1 t - V0 t := by sorry

end DevContest
