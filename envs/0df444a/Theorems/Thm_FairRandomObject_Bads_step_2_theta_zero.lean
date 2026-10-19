-- Prove2me | Theorems.Thm_FairRandomObject_Bads_step_2_theta_zero
-- name    : FairRandomObject.Bads.step_2_theta_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:00.875989+00:00
-- url     : https://prove2.me/theorems/3461e8c6-0c87-4013-bc9c-5b016fba7acf
-- title:
--   Step 2, p. 25 — for θ = 0 the inequalities (9) force Equal Split (on profiles with all x_i > 0)
-- statement:
--   Let $n\ge2$ and let $\varphi$ be an API rule satisfying the inequalities (9) with $\theta=0$, i.e. $\varphi_i(x)\le 1/n$ whenever $x_i>0$. Then at every profile $x$ with $x_i>0$ for all $i$,
--   $$\varphi(x)=\frac{e^N}{n}.$$
--
--   This is the case $\theta=0$ of Step 2 of the proof of Theorem 17.
--
--   **Formalization Note** The statement is restricted to profiles with all coordinates positive. At a profile with a zero coordinate, (9) only gives $\varphi_i(x)\le1$ for the zero agents, and the printed claim fails there: for $n=2$ and $x=(0,a)$ the share $(1,0)$ satisfies (9) with $\theta=0$.
-- source:
--   Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, proof of Theorem 17, Step 2

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

namespace FairRandomObject.Bads

/-- Bogomolnaia, Moulin, Sandomirskiy, On the Fair Division of a Random Object, arXiv:1903.10361v4, p. 25, Step 2 of the proof of Theorem 17: for `θ = 0`, the
inequalities (9) imply that `ϕ` is Equal Split.

**Formalization Note.** Stated on profiles with all `x_i > 0`. At a profile with a zero
coordinate, (9) with `x_i = 0` only says `ϕ_i ≤ 1` (convention `1/0 = +∞`), and the printed
claim fails there (`n = 2`, `x = (0, a)`, `ϕ(x) = (1, 0)`). -/
theorem step_2_theta_zero {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (h9 : Satisfies9 ϕ 0) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ϕ x = equalSplit n x := by sorry

end FairRandomObject.Bads
