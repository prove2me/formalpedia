-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_theorem_1
-- name    : BalkemaDeHaan.LimitTypes.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:20:58.420026+00:00
-- url     : https://prove2.me/theorems/7a75536d-7a8c-49b9-892b-13223b5b4281
-- title:
--   Theorem 1 — every nondegenerate weak limit of F_t(b(t) + xa(t)) is of type Π, Π_γ, Γ_α or Γ_{γ,α}
-- statement:
--   Let $F$ be a distribution function with $F(x) < 1$ for all $x$, and for $t \in \mathbb R$ let
--   $$F_t(x) = P\{X - t \le x \mid X > t\}$$
--   be the residual life distribution function (1) of a random variable $X$ with law $F$. Suppose there are functions $a(t) > 0$ and $b(t)$ such that the normalized residual life distributions converge weakly,
--   $$F_t\big(b(t) + x a(t)\big) \to G(x) \qquad \text{as } t \to \infty \text{ at every continuity point } x \text{ of } G,$$
--   to a nondegenerate distribution function $G$. Then $G$ is of type $\Pi$, $\Pi_\gamma$, $\Gamma_\alpha$ or $\Gamma_{\gamma,\alpha}$: there are $a > 0$, $b \in \mathbb R$ and a law $K$ among
--   $$\Pi, \quad \Pi_\gamma\ (\gamma > 0), \quad \Gamma_\alpha\ (\alpha > 0), \quad \Gamma_{\gamma,\alpha}\ (\gamma, \alpha > 0)$$
--   such that $G(x) = K(ax + b)$ for all $x$.
--
--   This is the classification of the limit laws of the residual life time at great age, the analogue for residual lives of the extremal types theorem; the paper's later sections determine the domains of attraction of these laws.
--
--   **Formalization Note** The law of $X$ is a probability measure $\mu$ on $\mathbb R$, and "$F(x) < 1$ for all $x$" is $\mu((x,\infty)) > 0$ for all $x$. The theorem uses the normalization of (1), which shifts $X - t$; the lemmas of §1 use (2), which shifts $X$, and the two differ by $b(t) \mapsto b(t) + t$. $G$ is the distribution function of a probability measure $\nu$ (so no mass escapes), and nondegenerate means $\nu$ is not a point mass; without nondegeneracy the statement is false, since $a(t) \to \infty$ gives the point mass at $0$ as a limit for every $F$. Weak convergence is required exactly at the continuity points of $G$, which matters because $\Pi_\gamma$ and $\Gamma_{\gamma,\alpha}$ have jumps. The paper writes the fourth family as $\Gamma_{\alpha,\gamma}$; it is the introduction's $\Gamma_{\gamma,\alpha}$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 796 (PDF 5), Theorem 1

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Theorem 1, p. 796 (PDF 5), in the convention (1): let `F` (the law `μ`) satisfy `F(x) < 1` for
all `x`, and let the normed residual life distribution functions `F_t(b(t) + x a(t))`, `a(t) > 0`,
converge weakly as `t → ∞` to a nondegenerate distribution function `G = cdf ν`. Then `G` is of
type `Π`, `Π_γ`, `Γ_α` or `Γ_{γ,α}`. -/
theorem theorem_1
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (a b : ℝ → ℝ) (ha : ∀ t : ℝ, 0 < a t)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ∀ c : ℝ, ν ≠ Measure.dirac c)
    (hconv : WeakConv (fun t x => residualCDF μ t (b t + x * a t)) (cdf ν)) :
    IsResidualLimitType (cdf ν) := by sorry

end BalkemaDeHaan.LimitTypes
