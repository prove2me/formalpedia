-- Prove2me | Theorems.Thm_CondBasedProd_bracket_maximizers_monotone
-- name    : CondBasedProd.bracket_maximizers_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:43.909947+00:00
-- url     : https://prove2.me/theorems/2adde2fa-aee6-485e-b9e2-b5902b2f990f
-- title:
--   (30)–(33), p.39: the maximizers of the bracket decrease in the marginal value (corrected: strong set order)
-- statement:
--   Let the model satisfy the standing assumptions and let $y\le y'$. If $s$ maximizes $r(\cdot)-f(\cdot)y$ over $\mathcal S$ and $s'$ maximizes $r(\cdot)-f(\cdot)y'$ over $\mathcal S$, then
--   $$
--   \min(s,s')\ \text{maximizes}\ r(\cdot)-f(\cdot)y',\qquad \max(s,s')\ \text{maximizes}\ r(\cdot)-f(\cdot)y.
--   $$
--
--   With $y=\lambda\Delta_\lambda(x,t)$ this is the step from the inequalities on $\Delta$ to the monotonicity of the optimal rates: in $x$ through Proposition 1, in $t$ through Proposition 2, and in $\lambda$ through the milestone on $\lambda\Delta_\lambda$.
--
--   Differences from the source:
--   - correction: (31) gives "any s > ŝ cannot be optimal for (x+1,t), hence s*(x+1,t) ≤ s*(x,t)" → the strong-set-order conclusion min(s,s′), max(s,s′); reason: (31) is a weak inequality; on S = [0,1], r(s) = f(s) = s, y = y′ = 1 every s is a maximizer, so the printed step fails for s < s′
--   - generalization: the three cases y = λΔ_λ(x,t), λΔ_λ(x+1,t), λΔ_λ(x,u) → arbitrary real y ≤ y′; reason: each printed case is the specialization to its values of y
-- source:
--   Drent, Drent & Arts, Condition-Based Production for Stochastically Deteriorating Systems, arXiv:2308.07507v2, App. A.9, displays (30)–(33), p.39

import Mathlib
import Definitions.Def_CondBasedProd_IsOptRate

namespace CondBasedProd

/-- **The maximizers of the bracket decrease in the marginal value** (arXiv:2308.07507v2, App. A.9,
(30)–(33), p.39): for `y ≤ y'`, if `s` maximizes `r(·) − f(·) y` and `s'` maximizes `r(·) − f(·) y'` over
`𝒮`, then `min s s'` maximizes the second and `max s s'` the first.

**Formalization Note.** Inequalities (31), (33) are weak, so the printed step "any `s > ŝ` cannot be
optimal" holds only in this strong-set-order form. Here `y` stands for `λ Δ_λ(x,t)`. -/
theorem bracket_maximizers_monotone (M : Model) (y y' s s' : ℝ) (hy : y ≤ y') (hs : IsBracketMax M y s) (hs' : IsBracketMax M y' s') : IsBracketMax M y' (min s s') ∧ IsBracketMax M y (max s s') := by sorry

end CondBasedProd
