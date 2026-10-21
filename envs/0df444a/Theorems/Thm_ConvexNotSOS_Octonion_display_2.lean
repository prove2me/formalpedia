-- Prove2me | Theorems.Thm_ConvexNotSOS_Octonion_display_2
-- name    : ConvexNotSOS.Octonion.display_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:49.723746+00:00
-- url     : https://prove2.me/theorems/77dce8e5-5687-4408-85c6-62105098d312
-- title:
--   Display (2) — octonionic Cauchy–Schwarz bounds and tight extrema
-- statement:
--   For every $k$ and all octonionic lists $x,y$ of length $k$, the Cauchy–Schwarz form satisfies
--
--   $$\tfrac14(\|x\|^2+\|y\|^2)^2\ge\|x\|^2\|y\|^2\ge\operatorname{cs}^{\mathbb O}_k(x,y)\ge0.$$
--
--   For $k\ge2$ the last and first bounds are attained on the Euclidean unit sphere, so $(\operatorname{cs}^{\mathbb O}_k)_{\min}=0$ and $(\operatorname{cs}^{\mathbb O}_k)_{\max}=1/4$. These constants enter the convexity correction for $q^{\mathbb O}_k$.
--
--   **Formalization Note.** The printed display says both inequalities are tight without qualifying $k$; at $k=1$ the form vanishes identically, so its maximum is $0$. The exact-extrema clause therefore has $k\ge2$, while the inequality holds for every $k$.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, p. 4, (2) and following sentence

import Definitions.Def_ConvexNotSOS_Octonion_Forms

namespace ConvexNotSOS.Octonion
open MvPolynomial

theorem display_2 (k : ℕ) :
    (∀ X : Matrix (Fin 16) (Fin k) ℝ,
      nx X * ny X ≤ (1 / 4 : ℝ) * (nx X + ny X) ^ 2 ∧
      csForm X ≤ nx X * ny X ∧ 0 ≤ csForm X) ∧
    (2 ≤ k → pmin (csPoly k) = 0 ∧ pmax (csPoly k) = 1 / 4) := by sorry
end ConvexNotSOS.Octonion
