-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_eq_3_26
-- name    : ConvexOptAlg.NesterovSmooth.eq_3_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:08.054989+00:00
-- url     : https://prove2.me/theorems/65dcd8f5-4cd5-4116-ae52-bf58b29e5e85
-- title:
--   Eq. (3.26), p. 295 — λ_{s+1}x_{s+1} − (λ_{s+1} − 1)y_{s+1} = λ_sy_{s+1} − (λ_s − 1)y_s
-- statement:
--   Let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent for the smooth case, with step sequences $(\lambda_t)$ and $(\gamma_t)$. Then for every $s\ge1$,
--
--   $$\lambda_{s+1}x_{s+1}-(\lambda_{s+1}-1)y_{s+1}=\lambda_sy_{s+1}-(\lambda_s-1)y_s.$$
--
--   The identity says that the vector $u_{s+1}=\lambda_{s+1}x_{s+1}-(\lambda_{s+1}-1)y_{s+1}-x^*$ coincides with the second vector on the right of (3.25), which makes (3.25) telescope. It is a rearrangement of the update rule $x_{s+1}=y_{s+1}+\gamma_s(y_s-y_{s+1})$ and uses no property of $f$.
--
--   **Formalization Note** No hypothesis on $f$ or $\beta$ is needed; the statement holds for any gradient map and any $\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, Eq. (3.26), p. 295

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- Eq. (3.26) (Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, p. 295): along a run of
Nesterov's accelerated gradient descent, for every `s ≥ 1`,
`λ_{s+1}x_{s+1} − (λ_{s+1} − 1)y_{s+1} = λ_s y_{s+1} − (λ_s − 1)y_s`. -/
theorem eq_3_26 {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (s : ℕ) (hs : 1 ≤ s) :
    lam (s + 1) • x (s + 1) - (lam (s + 1) - 1) • y (s + 1) =
      lam s • y (s + 1) - (lam s - 1) • y s := by sorry

end ConvexOptAlg.NesterovSmooth
