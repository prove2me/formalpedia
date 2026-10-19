-- Prove2me | Theorems.Thm_ConsHalving_Additive_step_3c_bounds
-- name    : ConsHalving.Additive.step_3c_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:45.485772+00:00
-- url     : https://prove2.me/theorems/fbad7f25-b893-4cfd-974e-d324b2507763
-- title:
--   Proof of Theorem 2.2, p. 5 — after Step 3(c), s ∈ [0,1]^m, unchanged where y_j = x_j, and s_{j*} ∈ {0, 1}
-- statement:
--   Let $x\in[0,1]^m$, let $y\in\mathbb R^m$, and let $j^*$ be an item with $y_{j^*}\ne x_{j^*}$ that minimizes $\gamma_j$ (Step 3(a)) over all items $j$ with $y_j\ne x_j$:
--   $$\gamma_{j^*}\le\gamma_j\qquad\text{whenever } y_j\ne x_j .$$
--   Let $s_j=(1-\gamma_{j^*})\,x_j+\gamma_{j^*}\,y_j$ (Step 3(c)). Then
--
--   1. $s_j\in[0,1]$ for every item $j$;
--   2. $s_j=x_j$ for every item $j$ with $y_j=x_j$;
--   3. $s_{j^*}\in\{0,1\}$.
--
--   Together with the previous milestone, this shows that one pass of the loop keeps the current point a consensus halving and uncuts item $j^*$.
--
--   **Formalization Note** $\gamma_j$ is used only on coordinates with $y_j\ne x_j$, as in the paper; the hypothesis $y_{j^*}\ne x_{j^*}$ is the paper's "$j^*=\operatorname{argmin}_{j\in M,\,y_j\ne x_j}\gamma_j$".
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, p. 5, proof of Theorem 2.2, 'Furthermore, for each j such that yj ≠ xj …'

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

namespace ConsHalving.Additive

theorem step_3c_bounds {m : ℕ} (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsFractional x) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsFractional (stepPoint x y (gamma x y jstar)) ∧
      (∀ j, y j = x j → stepPoint x y (gamma x y jstar) j = x j) ∧
      (stepPoint x y (gamma x y jstar) jstar = 0 ∨ stepPoint x y (gamma x y jstar) jstar = 1) := by sorry

end ConsHalving.Additive
