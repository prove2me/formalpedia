-- Prove2me | Theorems.Thm_ConvexOptAlg_ProjectedGD_thm_3_7_induction
-- name    : ConvexOptAlg.ProjectedGD.thm_3_7_induction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:52:38.328312+00:00
-- url     : https://prove2.me/theorems/bd53c2d3-1c06-43e6-9fbc-c42fc4ce6706
-- title:
--   Proof of Theorem 3.7, p. 271 — the recursion δ_{s+1}² ≤ 2βD²(δ_s − δ_{s+1}) gives δ_s ≤ (3βD² + δ₁)/s
-- statement:
--   Let $\beta>0$ and $D\in\mathbb R$, and let $(\delta_s)_{s\ge1}$ be real numbers with $\delta_s\ge0$ for all $s\ge1$ and
--   $$\delta_{s+1}^2\le2\beta D^2\,(\delta_s-\delta_{s+1})\qquad\text{for all }s\ge1 .$$
--   Then for every $s\ge1$,
--   $$\delta_s\le\frac{3\beta D^2+\delta_1}{s} .$$
--
--   This is the "easy induction" that closes the proof of Theorem 3.7, isolated as a fact about real sequences; there $D=\|x_1-x^*\|$ and $\delta_s=f(x_s)-f(x^*)$.
--
--   **Formalization Note** The hypothesis is the book's recursion $\delta_{s+1}\le\delta_s-\frac1{2\beta D^2}\delta_{s+1}^2$ multiplied by $2\beta D^2$, so the case $D=0$ needs no division. Nonnegativity of $\delta_s$ holds in the application because $x^*$ minimizes $f$ on $\mathcal X$ and the iterates lie in $\mathcal X$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Theorem 3.7, p. 271 (fourth display)

import Mathlib

namespace ConvexOptAlg.ProjectedGD

/-- The "easy induction" in the proof of Theorem 3.7 (Bubeck, arXiv:1405.4980v2, p. 271), as a
statement about real sequences: if `β > 0`, `D` is a real number, `δ_s ≥ 0` for `s ≥ 1` and
`δ_{s+1}² ≤ 2βD² (δ_s − δ_{s+1})` for every `s ≥ 1` (the recursion
`δ_{s+1} ≤ δ_s − (1/(2βD²)) δ_{s+1}²` multiplied out), then `δ_s ≤ (3βD² + δ_1)/s` for every
`s ≥ 1`. In the proof `D = ‖x₁ − x*‖`. -/
theorem thm_3_7_induction (β D : ℝ) (hβ : 0 < β) (δ : ℕ → ℝ)
    (hnonneg : ∀ s : ℕ, 1 ≤ s → 0 ≤ δ s)
    (hrec : ∀ s : ℕ, 1 ≤ s → δ (s + 1) ^ 2 ≤ 2 * β * D ^ 2 * (δ s - δ (s + 1)))
    (s : ℕ) (hs : 1 ≤ s) :
    δ s ≤ (3 * β * D ^ 2 + δ 1) / s := by sorry

end ConvexOptAlg.ProjectedGD
