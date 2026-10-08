-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_eq_6_1
-- name    : ConvexOptAlg.SVRG.eq_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:45:36.697853+00:00
-- url     : https://prove2.me/theorems/c2c22925-8ef1-4dfb-8a94-07ddd50065aa
-- title:
--   Equation (6.1), p. 337 — one SVRG epoch contracts by 0.9
-- statement:
--   Let $m\ge1$, let $f_i$ be convex and $\beta$-smooth, and let their average $f$ be $\alpha$-strongly convex with minimizer $x^*$, where $\alpha,\beta>0$. Start an SVRG epoch at any $y$, use step size $\eta=1/(10\beta)$, and take an integer epoch length $k=20\beta/\alpha$. If $y^+$ averages the first $k$ inner iterates, then
--
--   $$\mathbb E\,f(y^+)-f(x^*)\le0.9\bigl(f(y)-f(x^*)\bigr).$$
--
--   The expectation is over the $k$ independent uniform indices within this one epoch. This contraction is the repeated step in Theorem 6.5.
--
--   **Formalization Note** The book writes $k=20\kappa$ with $\kappa=\beta/\alpha$; since $k$ counts iterations, the theorem assumes this value is an integer.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (6.1), p. 337, PDF p. 110, proved p. 338

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- Equation (6.1), p. 337: one full epoch contracts the expected objective
gap by `0.9` at the stated step size and epoch length. -/
theorem eq_6_1 {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (k : ℕ) (y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hα : 0 < α) (hβ : 0 < β)
    (hkexact : (k : ℝ) = 20 * (β / α))
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin k → Fin m =>
        objective fs (epochOut gs (1 / (10 * β)) k y idx)) -
        objective fs xstar ≤
      (9 / 10 : ℝ) * (objective fs y - objective fs xstar) := by sorry

end ConvexOptAlg.SVRG
