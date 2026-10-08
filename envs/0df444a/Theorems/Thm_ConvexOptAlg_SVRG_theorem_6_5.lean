-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_theorem_6_5
-- name    : ConvexOptAlg.SVRG.theorem_6_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:45:47.961214+00:00
-- url     : https://prove2.me/theorems/da01f7ae-4271-4789-b9b3-e0a00854f416
-- title:
--   Theorem 6.5, p. 336 — SVRG contracts by 0.9 per epoch
-- statement:
--   Let $m\ge1$, let each $f_i:\mathbb R^n\to\mathbb R$ be convex with $\beta$-Lipschitz gradient, and let their average $f$ be $\alpha$-strongly convex with minimizer $x^*$, where $\alpha,\beta>0$. Start SVRG at any $y^{(1)}$, use $\eta=1/(10\beta)$ and the integer epoch length $k=20\kappa$ with $\kappa=\beta/\alpha$. Each epoch samples $k$ independent uniform indices and returns the average of its first $k$ inner iterates. For every $s\ge1$,
--
--   $$\mathbb E\,f(y^{(s+1)})-f(x^*)\le0.9^s\bigl(f(y^{(1)})-f(x^*)\bigr).$$
--
--   This is the linear convergence guarantee for the variance-reduced algorithm. The expectation includes every sampled index in the first $s$ epochs.
--
--   **Formalization Note** The book's standing convention assumes $x^*$ exists. Its $k=20\kappa$ implicitly requires $20\beta/\alpha\in\mathbb N$; Lean states this as an equality with a natural-number $k$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 6.5, p. 336, PDF p. 109

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- Theorem 6.5, p. 336. Expectation is over the `s*k` independent uniform
component indices used in the first `s` epochs; `epochOutput s` is `y⁽ˢ⁺¹⁾`. -/
theorem theorem_6_5 {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (k s : ℕ) (y₁ xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hs : 1 ≤ s)
    (hα : 0 < α) (hβ : 0 < β)
    (hkexact : (k : ℝ) = 20 * (β / α))
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin s → Fin k → Fin m =>
        objective fs (epochOutput gs (1 / (10 * β)) y₁ s idx)) -
        objective fs xstar ≤
      (9 / 10 : ℝ) ^ s * (objective fs y₁ - objective fs xstar) := by sorry

end ConvexOptAlg.SVRG
