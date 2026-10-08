-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_eq_3_19
-- name    : ConvexOptAlg.NesterovStrong.eq_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:00:04.96399+00:00
-- url     : https://prove2.me/theorems/f91823b5-7bf1-4fed-b66c-7b4c6936c050
-- title:
--   Eq. (3.19), p. 291 — f(y_s) ≤ min_{x ∈ ℝⁿ} Φ_s(x)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with $\alpha,\beta>0$, $\kappa=\beta/\alpha$, and let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent with the functions $\Phi_s$ of (3.17). Then for every $s\ge1$,
--   $$f(y_s)\le\min_{x\in\mathbb R^n}\Phi_s(x).$$
--
--   This measures how far below $f$ the model $\Phi_s$ can lie: its minimum value is still at least the value of the current iterate $y_s$. Together with (3.18) it yields the rate of Theorem 3.18.
--
--   **Formalization Note** The minimum is stated without an infimum: the Lean statement says $f(y_s)\le\Phi_s(x)$ for every $x\in\mathbb R^n$. The minimum exists since $\Phi_s$ is a strongly convex quadratic (milestone `eq_3_21_form`).
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.18, Eq. (3.19), p. 291

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, proof of Theorem 3.18, Eq. (3.19), p. 291: for a `β`-smooth, `α`-strongly convex
`f` on `ℝⁿ` and a run `(x, y)` of Nesterov's accelerated gradient descent,
`f(y_s) ≤ min_{z ∈ ℝⁿ} Φ_s(z)` for every `s ≥ 1`, stated as `f(y_s) ≤ Φ_s(z)` for every `z`. -/
theorem eq_3_19 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (hs : 1 ≤ s) (z : EuclideanSpace ℝ (Fin n)) :
    f (y s) ≤ Phi f g α β x s z := by sorry

end ConvexOptAlg.NesterovStrong
