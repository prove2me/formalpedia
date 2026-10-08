-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_eq_3_18
-- name    : ConvexOptAlg.NesterovStrong.eq_3_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:00:16.689158+00:00
-- url     : https://prove2.me/theorems/67ad69c3-b11f-40f7-bc3c-786f707d6b1a
-- title:
--   Eq. (3.18), p. 291 — Φ_{s+1}(x) ≤ f(x) + (1 − 1/√κ)^s (Φ₁(x) − f(x))
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be $\alpha$-strongly convex and $\beta$-smooth with $\alpha,\beta>0$, and put $\kappa=\beta/\alpha$. Let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent and let $\Phi_s$ be the functions defined from the points $x_s$ by (3.17). Then for every $s\ge0$ and every $x\in\mathbb R^n$,
--   $$\Phi_{s+1}(x)\le f(x)+\Big(1-\frac1{\sqrt\kappa}\Big)^s\big(\Phi_1(x)-f(x)\big).$$
--
--   The functions $\Phi_s$ thus approach $f$ from below at the geometric rate $(1-1/\sqrt\kappa)^s$; this is one half of the estimate-sequence argument for Theorem 3.18.
--
--   **Formalization Note** The inequality is stated for every $s\ge0$; at $s=0$ it is an equality. The positivity $\beta>0$ is implied by the other hypotheses whenever $n\ge1$ and is stated for definiteness of $\kappa$.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.18, Eq. (3.18), p. 291

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, proof of Theorem 3.18, Eq. (3.18), p. 291: for a `β`-smooth, `α`-strongly convex
`f` on `ℝⁿ` (gradient map `g`, `κ = β/α`) and a run `(x, y)` of Nesterov's accelerated gradient
descent, the functions `Φ_s` of (3.17) satisfy
`Φ_{s+1}(z) ≤ f(z) + (1 − 1/√κ)^s (Φ₁(z) − f(z))` for every `z` and every `s`. -/
theorem eq_3_18 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsc : OnlineConvexOpt.ConvexBasics.StronglyConvexOn Set.univ f g α)
    (hsm : IsBetaSmooth f g β)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovSCRun g α β x y)
    (s : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    Phi f g α β x (s + 1) z ≤
      f z + (1 - 1 / Real.sqrt (kappa α β)) ^ s * (Phi f g α β x 1 z - f z) := by sorry

end ConvexOptAlg.NesterovStrong
