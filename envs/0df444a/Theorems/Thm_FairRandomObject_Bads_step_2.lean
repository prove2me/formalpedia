-- Prove2me | Theorems.Thm_FairRandomObject_Bads_step_2
-- name    : FairRandomObject.Bads.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:52.963962+00:00
-- url     : https://prove2.me/theorems/da2eaed5-9bc8-4a80-8036-bd3e84ed5164
-- title:
--   Step 2, p. 25 — if a symmetric API rule ϕ satisfies (9) with θ ∈ (0, 1], then ϕ^θ dominates ϕ or equals ϕ
-- statement:
--   Let $n\ge2$, $0<\theta\le1$, and let $\varphi$ be a symmetric API rule satisfying the inequalities (9) with parameter $\theta$. Then either $\varphi(x)=\varphi^\theta(x)$ for every $x\in\mathbb R^N_+$, or $\varphi^\theta$ dominates $\varphi$:
--   $$\sum_{i\in N}\varphi^\theta_i(x)\,x_i\le\sum_{i\in N}\varphi_i(x)\,x_i\quad\text{for all }x\in\mathbb R^N_+,$$
--   with strict inequality for some $x\in\mathbb R^N_+$.
--
--   Among the rules obeying a given bound (9), the Bottom-Heavy rule with the same parameter is therefore the cheapest.
--
--   **Formalization Note** The case $\theta=0$ is handled separately (Step 2 says "from now on, we assume that $\theta>0$"). Symmetry of $\varphi$ is assumed: the proof uses it on the ray through $e^N$ and in the equality case, although the printed sentence omits it.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, proof of Theorem 17, Step 2

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

namespace FairRandomObject.Bads

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, Step 2 of the proof of Theorem 17 (case `θ > 0`): if the
symmetric API rule `ϕ` satisfies the inequalities (9) for some `θ ∈ (0, 1]`, then the
Bottom-Heavy rule `ϕ^θ` either equals `ϕ` on `ℝ^N_+` or dominates it (for a bad).

**Formalization Note.** `θ > 0` is the proof's "From now on, we assume that θ > 0"; the case
`θ = 0` is `step_2_theta_zero`. Symmetry of `ϕ` is used by the proof (along the ray through
`e^N` and in the equality case) and is a hypothesis, although the printed sentence omits it. -/
theorem step_2 {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ϕ : Rule n)
    (hϕ : IsAPIRule ϕ) (hsym : IsSymmetric ϕ) (h9 : Satisfies9 ϕ θ) :
    (∀ x : Fin n → ℝ, 0 ≤ x → ϕ x = bottomHeavy n θ x) ∨ DominatesBad (bottomHeavy n θ) ϕ := by sorry

end FairRandomObject.Bads
