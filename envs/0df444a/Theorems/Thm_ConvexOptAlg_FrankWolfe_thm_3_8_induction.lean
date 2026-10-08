-- Prove2me | Theorems.Thm_ConvexOptAlg_FrankWolfe_thm_3_8_induction
-- name    : ConvexOptAlg.FrankWolfe.thm_3_8_induction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:02:20.710371+00:00
-- url     : https://prove2.me/theorems/a3cf17b9-df5d-49d9-a80a-eb8f5c5ffef2
-- title:
--   §3.3, proof of Theorem 3.8, p. 273 — the induction with γ_s = 2/(s + 1) gives δ_t ≤ 2βR²/(t + 1)
-- statement:
--   Let $\beta\ge0$ and $R\in\mathbb R$, and let $(\delta_t)$ be a sequence of real numbers with
--   $$\delta_2\le\frac{\beta}{2}R^2\quad\text{and}\quad\delta_{s+1}\le\Bigl(1-\frac{2}{s+1}\Bigr)\delta_s+\frac{\beta}{2}\Bigl(\frac{2}{s+1}\Bigr)^2R^2\ \text{ for every } s\ge2 .$$
--   Then for every $t\ge2$,
--   $$\delta_t\le\frac{2\beta R^2}{t+1}.$$
--
--   This is the "simple induction using that $\gamma_s=2/(s+1)$" that finishes the proof of Theorem 3.8 once the one-step recursion and the initialization are known. It is a statement about real sequences only.
--
--   **Formalization Note** The recursion is assumed only from $s=2$ on, since the induction starts at step 2. $\beta\ge0$ is the usual reading of "β-smooth"; without it the base case of the bound can fail.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.3, proof of Theorem 3.8, p. 273 ("A simple induction using that γ_s = 2/(s+1) finishes the proof")

import Mathlib

namespace ConvexOptAlg.FrankWolfe

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.8, p. 273 ("A simple induction using that
`γ_s = 2/(s+1)` finishes the proof"): a real sequence with `δ₂ ≤ (β/2)R²` and
`δ_{s+1} ≤ (1 − γ_s)δ_s + (β/2)γ_s²R²`, `γ_s = 2/(s+1)`, for every `s ≥ 2` satisfies
`δ_t ≤ 2βR²/(t + 1)` for every `t ≥ 2`. -/
theorem thm_3_8_induction (δ : ℕ → ℝ) (β R : ℝ) (hβ : 0 ≤ β)
    (h2 : δ 2 ≤ β / 2 * R ^ 2)
    (hrec : ∀ s : ℕ, 2 ≤ s →
      δ (s + 1) ≤ (1 - 2 / ((s : ℝ) + 1)) * δ s + β / 2 * (2 / ((s : ℝ) + 1)) ^ 2 * R ^ 2)
    (t : ℕ) (ht : 2 ≤ t) :
    δ t ≤ 2 * β * R ^ 2 / ((t : ℝ) + 1) := by sorry

end ConvexOptAlg.FrankWolfe
