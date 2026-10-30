-- Prove2me | Theorems.Thm_DDROFB_theorem_1a
-- name    : DDROFB.theorem_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:50.836961+00:00
-- url     : https://prove2.me/theorems/07ff570e-cad3-4b2f-b468-0627f87a9b3b
-- title:
--   Theorem 1(a): $\delta^*(\cdot\mid\mathcal U) \ge \mathrm{VaR}^{\mathbb P}_\epsilon$ implies a probabilistic guarantee
-- statement:
--   Let $\mathbb P$ be a probability measure on $\mathbb R^d$, let $\epsilon > 0$, and let $\mathcal U \subseteq \mathbb R^d$ be nonempty, convex and compact. If
--
--   $$
--   \delta^*(v \mid \mathcal U) \;\ge\; \mathrm{VaR}^{\mathbb P}_\epsilon(v) \qquad \text{for all } v \in \mathbb R^d,
--   $$
--
--   then $\mathcal U$ implies a probabilistic guarantee for $\mathbb P$ at level $\epsilon$: for every concave $g : \mathbb R^d \to \mathbb R$ with $g \le 0$ on $\mathcal U$, $\mathbb P(g(\tilde u) \le 0) \ge 1-\epsilon$.
--
--   This is the geometric characterization on which the paper's schema rests: to build a set that implies a guarantee for every concave constraint, it suffices to bound the Value at Risk in each direction by the support function.
--
--   Differences from the source:
--   - encoding: measure P → probability measure P on ℝ^d; reason: P is the law of the random vector ũ, and the conclusion P(·) ≥ 1 − ε is a probability statement
--   - encoding: for every x and every f(u,x) concave in u → every concave g : ℝ^d → ℝ (ImpliesGuarantee); reason: x∗ is fixed in (2), so only g = f(·,x∗) matters, and every concave g is f(·,x∗) for f(u,x) := g(u)
--   - encoding: level ϵ (standing "Given ϵ > 0", p. 2) → hypothesis 0 < ε; reason: the paper's standing assumption written as a binder
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 1(a), p. 10 (proof p. ec1)

import Mathlib
import Definitions.Def_DDROFB_supportFn
import Definitions.Def_DDROFB_VaR
import Definitions.Def_DDROFB_ImpliesGuarantee
open MeasureTheory

namespace DDROFB

/-- **Theorem 1(a): a support function dominating VaR implies a probabilistic guarantee.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 1(a),
p. 10: "Suppose `U` is nonempty, convex and compact. Then, `U` implies a probabilistic guarantee at
level `ϵ` for `P` for every `f(u,x)` concave in `u` for every `x` if
`δ∗(v| U) ≥ VaR^P_ϵ(v) ∀v ∈ ℝ^d`." (Proof on p. ec1.)

**Formalization Note.** `P` is a probability measure on `ℝ^d = EuclideanSpace ℝ (Fin d)` (the law
of `ũ`), and `0 < ε` is the paper's standing "Given `ϵ > 0`" (p. 2). "Implies a probabilistic
guarantee for every `f` concave in `u`" is `ImpliesGuarantee U P ε`, which quantifies over every
concave `g = f(·, x∗)`. For `ε ≥ 1` the conclusion holds trivially, so no upper bound on `ε` is
added. -/
theorem theorem_1a {d : ℕ} (U : Set (EuclideanSpace ℝ (Fin d))) (hne : U.Nonempty)
    (hconv : Convex ℝ U) (hcomp : IsCompact U)
    (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P] (ε : ℝ) (hε : 0 < ε)
    (h : ∀ v : EuclideanSpace ℝ (Fin d), VaR P ε v ≤ supportFn U v) :
    ImpliesGuarantee U P ε := by sorry

end DDROFB
