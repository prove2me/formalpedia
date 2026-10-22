-- Prove2me | Theorems.Thm_FairRandomObject_Bads_proposition_14
-- name    : FairRandomObject.Bads.proposition_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:47.876151+00:00
-- url     : https://prove2.me/theorems/a8c38f68-ab9c-402b-b9d2-44ce88a86e10
-- title:
--   Proposition 14, p. 15 — a symmetric API rule for a bad satisfies Fair Share iff (9) holds for some θ ∈ [0, 1]
-- statement:
--   Let $n\ge2$ and let $\varphi$ be a symmetric API rule dividing a bad. Then $\varphi$ satisfies Fair Share if and only if there is a number $\theta$ with $0\le\theta\le1$ such that
--   $$\varphi_i(x)\le\min\Big\{\frac1n+\frac{\theta}{n-1}\Big(\frac{\bar x}{x_i}-1\Big),\,1\Big\}\qquad\text{for all }i\in N,\ x\in\mathbb R^N_+,\tag{9}$$
--   where $1/0=+\infty$.
--
--   This characterizes fairness pointwise, without reference to any prior, and is the starting point of the proof of Theorem 17.
--
--   **Formalization Note** The bound is $1$ whenever $x_i=0$, for every $\theta$ including $\theta=0$. Reading $0\cdot\infty=0$ at $\theta=0$ instead would make the "only if" direction false.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 15, Proposition 14

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

namespace FairRandomObject.Bads

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 15, Proposition 14: a symmetric API rule `ϕ` dividing a bad
satisfies Fair Share if and only if there is `θ ∈ [0, 1]` with
`ϕ_i(x) ≤ min{1/n + θ/(n−1)(x̄/x_i − 1), 1}` for all `i ∈ N` and `x ∈ ℝ^N_+` (9), where `1/0 = +∞`.

**Formalization Note.** `bound9` is `1` whenever `x_i = 0`, for every `θ` (including `θ = 0`);
this is the reading of `1/0 = +∞` under which the proposition holds. -/
theorem proposition_14 {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (hsym : IsSymmetric ϕ) :
    FairShareBad ϕ ↔ ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ Satisfies9 ϕ θ := by sorry

end FairRandomObject.Bads
