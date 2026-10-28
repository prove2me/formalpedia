-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_eq_17_19_radius
-- name    : ChanceStateCtrl.General.eq_17_19_radius
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:30.404797+00:00
-- url     : https://prove2.me/theorems/882ebe38-98f9-4fe4-a023-26621715f1c3
-- title:
--   (17)–(19), p. 6 — {r ≥ 0 | g(u, rΣ^{1/2}v) ≤ 0} = [0, ρ(u, v)], g = 0 at ρ, and e(u, v) = F_η(ρ(u, v)) or 1
-- statement:
--   Assume Assumption 2.1 and let $u\in U$ satisfy $g(u,0)<0$ (as every $u$ in the neighbourhood $\mathcal N(\bar u)$ of p. 6 does). For every $v\in\mathbb S^{m-1}$, with $\rho(u,v)=\sup\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}\in[0,\infty]$:
--
--   1. if $\rho(u,v)<\infty$, then $\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}=[0,\rho(u,v)]$ (17), $\rho(u,v)$ solves $g(u,r\Sigma^{1/2}v)=0$ (18) and is its only solution $r\ge0$, and $e(u,v)=F_\eta(\rho(u,v))$;
--   2. if $\rho(u,v)=\infty$, then $\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}=[0,\infty)$ and $e(u,v)=1$.
--
--   Items 1 and 2 together are the representation
--   $$
--   e(u,v)=\begin{cases}F_\eta(\rho(u,v))&\text{if }\rho(u,v)<\infty,\\ 1&\text{if }\rho(u,v)=\infty,\end{cases}\tag{19}
--   $$
--   where $F_\eta$ is the distribution function of the chi distribution with $m$ degrees of freedom.
--
--   The radius function is the device through which convexity of $g$ is transferred to the radial probability function in Lemma 2.3.
--
--   **Formalization Note** The page calls $\rho(u,v)$ "the unique solution in $r$" of (18); since (17) concerns $r\ge0$, uniqueness is stated among $r\ge0$ (for $r<0$ the equation describes the opposite ray and may have another solution).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 6, (17), (18), (19)

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem eq_17_19_radius {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (u : U) (hu : g u 0 < 0) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    (radius Sigma g u v < ⊤ →
      {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} =
          Set.Icc 0 (radius Sigma g u v).toReal ∧
        g u ((radius Sigma g u v).toReal • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) = 0 ∧
        (∀ r : ℝ, 0 ≤ r → g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) = 0 →
          r = (radius Sigma g u v).toReal) ∧
        radialProb Sigma g u v = chiCDF m (radius Sigma g u v).toReal) ∧
    (radius Sigma g u v = ⊤ →
      {r : ℝ | 0 ≤ r ∧ g u (r • sqrtCov Sigma (v : EuclideanSpace ℝ (Fin m))) ≤ 0} = Set.Ici 0 ∧
        radialProb Sigma g u v = 1) := by sorry

end ChanceStateCtrl.General
