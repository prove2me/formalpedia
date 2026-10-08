-- Prove2me | Theorems.Thm_ConvexOptAlg_SVRG_epoch_bound
-- name    : ConvexOptAlg.SVRG.epoch_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:45:36.965857+00:00
-- url     : https://prove2.me/theorems/0b73df9c-f549-476a-8be4-7055a343edc5
-- title:
--   §6.3, p. 338 — general one-epoch gap bound
-- statement:
--   Let $m,k\ge1$, let each component $f_i$ be convex and $\beta$-smooth, and suppose their average $f$ is $\alpha$-strongly convex with minimizer $x^*$, where $\alpha,\beta>0$. For an anchor $y$ and a step size $0<\eta<1/(2\beta)$, run an SVRG epoch and average the first $k$ inner iterates to obtain $y^+$. Then
--
--   $$\mathbb E\,f(y^+)-f(x^*)\le\left(\frac{1}{\alpha\eta(1-2\beta\eta)k}+\frac{2\beta\eta}{1-2\beta\eta}\right)\bigl(f(y)-f(x^*)\bigr).$$
--
--   The expectation is over all $k$ independent uniform component indices in the epoch. This is the general contraction formula before the constants of Theorem 6.5 are substituted.
--
--   **Formalization Note** Strong convexity uses the published `StronglyConvexOn` definition on all of $\mathbb R^n$. The condition $2\beta\eta<1$ makes the denominators positive.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.3, p. 338, PDF p. 111, unnumbered rearranged epoch display

import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- The rearranged one-epoch inequality on p. 338, before substituting
`η = 1/(10β)` and `k = 20β/α`. The expectation is over all `k` samples. -/
theorem epoch_bound {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β η : ℝ) (k : ℕ) (y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hα : 0 < α) (hβ : 0 < β)
    (hη : 0 < η) (hηsmall : 2 * β * η < 1)
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin k → Fin m => objective fs (epochOut gs η k y idx)) -
        objective fs xstar ≤
      (1 / (α * η * (1 - 2 * β * η) * (k : ℝ)) +
        2 * β * η / (1 - 2 * β * η)) *
        (objective fs y - objective fs xstar) := by sorry

end ConvexOptAlg.SVRG
