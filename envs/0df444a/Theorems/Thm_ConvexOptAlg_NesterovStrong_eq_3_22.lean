-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_eq_3_22
-- name    : ConvexOptAlg.NesterovStrong.eq_3_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:00:51.694617+00:00
-- url     : https://prove2.me/theorems/7e6c14bf-a0b9-45d7-b51a-d3324db180b4
-- title:
--   Eq. (3.22), p. 292 — Φ*_{s+1} + (α/2)‖x_s − v_{s+1}‖² = (1 − 1/√κ)Φ*_s + (α/2)(1 − 1/√κ)‖x_s − v_s‖² + f(x_s)/√κ
-- statement:
--   Let $\alpha>0$, $\beta\in\mathbb R$, $\kappa=\beta/\alpha$, let $f$, $g$ (in the role of $\nabla f$) and the points $(x_s)_{s\ge1}$ be arbitrary, and let $\Phi_s$, $v_s$ and $\Phi^*_s=\Phi_s(v_s)$ be as in (3.17) and (3.21). Then for every $s\ge1$,
--   $$\Phi^*_{s+1}+\frac\alpha2\|x_s-v_{s+1}\|^2=\Big(1-\frac1{\sqrt\kappa}\Big)\Phi^*_s+\frac\alpha2\Big(1-\frac1{\sqrt\kappa}\Big)\|x_s-v_s\|^2+\frac1{\sqrt\kappa}f(x_s).$$
--
--   This identity, obtained by evaluating $\Phi_{s+1}$ at $x_s$, gives a closed recursion for the minimum values $\Phi^*_s$.
--
--   **Formalization Note** Like `eq_3_21_form`, the identity is algebraic and is stated for any sequence of points and any map $g$.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.18, Eq. (3.22), p. 292

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, proof of Theorem 3.18, Eq. (3.22), p. 292: for any `α > 0`, any `f`, gradient map
`g`, `β`, any sequence of points `x_s` and every `s ≥ 1`,
`Φ∗_{s+1} + (α/2)‖x_s − v_{s+1}‖² = (1 − 1/√κ)Φ∗_s + (α/2)(1 − 1/√κ)‖x_s − v_s‖² + (1/√κ) f(x_s)`. -/
theorem eq_3_22 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (s : ℕ) (hs : 1 ≤ s) :
    PhiStar f g α β x (s + 1) + α / 2 * ‖x s - v g α β x (s + 1)‖ ^ 2 =
      (1 - 1 / Real.sqrt (kappa α β)) * PhiStar f g α β x s +
        α / 2 * (1 - 1 / Real.sqrt (kappa α β)) * ‖x s - v g α β x s‖ ^ 2 +
          1 / Real.sqrt (kappa α β) * f (x s) := by sorry

end ConvexOptAlg.NesterovStrong
