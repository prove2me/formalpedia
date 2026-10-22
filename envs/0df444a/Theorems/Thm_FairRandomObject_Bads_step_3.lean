-- Prove2me | Theorems.Thm_FairRandomObject_Bads_step_3
-- name    : FairRandomObject.Bads.step_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:49.966801+00:00
-- url     : https://prove2.me/theorems/2aca95cf-ea33-4745-aead-0f54678d3f37
-- title:
--   Step 3, p. 26 — ϕ^{θ⁺} dominates ϕ^{θ⁻} if 1 ≥ θ⁺ > θ⁻ > 0
-- statement:
--   Let $n\ge2$ and $0<\theta^-<\theta^+\le1$. Then the Bottom-Heavy rule $\varphi^{\theta^+}$ dominates $\varphi^{\theta^-}$:
--   $$\sum_{i\in N}\varphi^{\theta^+}_i(x)\,x_i\le\sum_{i\in N}\varphi^{\theta^-}_i(x)\,x_i\quad\text{for all }x\in\mathbb R^N_+,$$
--   with strict inequality for some $x\in\mathbb R^N_+$.
--
--   Within the Bottom-Heavy family, a larger parameter is always more efficient; in particular $\varphi^1$ dominates every $\varphi^\theta$ with $0<\theta<1$.
--
--   **Formalization Note** The paper proves the inequality on profiles with distinct coordinates and extends it by continuity; the statement covers all of $\mathbb R^N_+$. The upper bound $\theta^+\le1$ is the range of the family.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 26, proof of Theorem 17, Step 3

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

namespace FairRandomObject.Bads

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 26, Step 3 of the proof of Theorem 17: if `θ⁺ > θ⁻ > 0` (and
`θ⁺ ≤ 1`, the range of the family), then `ϕ^{θ⁺}` dominates `ϕ^{θ⁻}` (for a bad): its social
cost is at most that of `ϕ^{θ⁻}` at every `x ∈ ℝ^N_+` and strictly lower at some `x ∈ ℝ^N_+`.

**Formalization Note.** The proof treats profiles with distinct coordinates and extends by
continuity of the total disutility; the statement is over all of `ℝ^N_+`. -/
theorem step_3 {n : ℕ} (hn : 2 ≤ n) (θm θp : ℝ) (hm : 0 < θm) (hmp : θm < θp) (hp : θp ≤ 1) :
    DominatesBad (bottomHeavy n θp) (bottomHeavy n θm) := by sorry

end FairRandomObject.Bads
