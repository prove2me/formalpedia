-- Prove2me | Theorems.Thm_ConvexOptAlg_LowerBounds_thm_3_14_final_bound
-- name    : ConvexOptAlg.LowerBounds.thm_3_14_final_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:44:43.391617+00:00
-- url     : https://prove2.me/theorems/8549c333-7d3e-425b-b839-0d25d19cbcfc
-- title:
--   Proof of Theorem 3.14, p. 283 — f*_t − f*_{2t+1} = (β/8)(1/(t+1) − 1/(2t+2)) ≥ (3β/32)‖x*_{2t+1}‖²/(t+1)²
-- statement:
--   Let $\beta>0$, $t\ge1$ and $2t+1\le n$. With $f_k(x)=\frac\beta8x^\top A_kx-\frac\beta4x^\top e_1$, $f_k^*=\inf_{x\in\mathbb R^n}f_k(x)$ and $x^*_k$ as in the previous items,
--   $$f_t^*-f_{2t+1}^*=\frac\beta8\Bigl(\frac1{t+1}-\frac1{2t+2}\Bigr)\ge\frac{3\beta}{32}\,\frac{\|x^*_{2t+1}\|^2}{(t+1)^2}.$$
--
--   This is the last step of the proof of Theorem 3.14: the gap between the value reachable after $t$ queries and the true optimum, compared with the squared distance from the start to the optimum.
--
--   **Formalization Note** $t\ge1$ is the standing side condition of Theorem 3.14 (its minimum over $1\le s\le t$ is empty otherwise).
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 283

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.LowerBounds

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 283 (closing display). With
`f*_k = inf_{x∈ℝⁿ} f_k(x)`, for `1 ≤ t`, `2t + 1 ≤ n` and `β > 0`:
`f*_t − f*_{2t+1} = (β/8)(1/(t+1) − 1/(2t+2)) ≥ (3β/32) ‖x*_{2t+1}‖²/(t+1)²`. -/
theorem thm_3_14_final_bound (n t : ℕ) (β : ℝ) (hβ : 0 < β) (ht : 1 ≤ t) (htn : 2 * t + 1 ≤ n) :
    (⨅ y, fK n β t y) - (⨅ y, fK n β (2 * t + 1) y) =
        β / 8 * (1 / ((t : ℝ) + 1) - 1 / (2 * (t : ℝ) + 2)) ∧
      β / 8 * (1 / ((t : ℝ) + 1) - 1 / (2 * (t : ℝ) + 2)) ≥
        3 * β / 32 * (‖xstarK n (2 * t + 1)‖ ^ 2 / ((t : ℝ) + 1) ^ 2) := by sorry

end ConvexOptAlg.LowerBounds
