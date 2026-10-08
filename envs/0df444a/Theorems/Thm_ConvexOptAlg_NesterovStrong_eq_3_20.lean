-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_eq_3_20
-- name    : ConvexOptAlg.NesterovStrong.eq_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:01:03.333614+00:00
-- url     : https://prove2.me/theorems/c3ae2e72-06b2-427a-98f2-a9533cbcacdf
-- title:
--   Eq. (3.20), p. 292 — Φ*_{s+1} ≥ (1 − 1/√κ)Φ*_s + (1 − 1/√κ)∇f(x_s)⊤(x_s − y_s) + f(x_s)/√κ − ‖∇f(x_s)‖²/(2β)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with $\alpha,\beta>0$, $\kappa=\beta/\alpha$, let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent, and let $\Phi^*_s=\Phi_s(v_s)=\min\Phi_s$ with $\Phi_s$, $v_s$ as in (3.17), (3.21). Then for every $s\ge1$,
--   $$\Phi^*_{s+1}\ge\Big(1-\frac1{\sqrt\kappa}\Big)\Phi^*_s+\Big(1-\frac1{\sqrt\kappa}\Big)\nabla f(x_s)^\top(x_s-y_s)+\frac1{\sqrt\kappa}f(x_s)-\frac1{2\beta}\|\nabla f(x_s)\|^2 .$$
--
--   This is the inductive step of (3.19): its right-hand side is an upper bound on $f(y_{s+1})$ obtained from smoothness, convexity and the induction hypothesis.
--
--   **Formalization Note** $\Phi^*_s$ is the value of $\Phi_s$ at $v_s$, which equals the book's $\min\Phi_s$ by `eq_3_21_form`.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.18, Eq. (3.20), p. 292

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, proof of Theorem 3.18, Eq. (3.20), p. 292: for a `β`-smooth, `α`-strongly convex
`f` on `ℝⁿ` and a run `(x, y)` of Nesterov's accelerated gradient descent, for every `s ≥ 1`,
`Φ∗_{s+1} ≥ (1 − 1/√κ)Φ∗_s + (1 − 1/√κ)∇f(x_s)ᵀ(x_s − y_s) + (1/√κ) f(x_s) − (1/(2β))‖∇f(x_s)‖²`. -/
theorem eq_3_20 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (hs : 1 ≤ s) :
    PhiStar f g α β x (s + 1) ≥
      (1 - 1 / Real.sqrt (kappa α β)) * PhiStar f g α β x s +
        (1 - 1 / Real.sqrt (kappa α β)) * ⟪g (x s), x s - y s⟫_ℝ +
          1 / Real.sqrt (kappa α β) * f (x s) - 1 / (2 * β) * ‖g (x s)‖ ^ 2 := by sorry

end ConvexOptAlg.NesterovStrong
