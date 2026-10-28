-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_e_lipschitz_bounded
-- name    : ChanceStateCtrl.General.theorem_2_2_e_lipschitz_bounded
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-25T01:19:58.974551+00:00
-- url     : https://prove2.me/theorems/0241a24f-5f02-41ce-bdef-e7e3e628d18c
-- title:
--   Theorem 2.2 (Lipschitz part, case M bounded), p. 5 — e(·, v) uniformly locally Lipschitz around ū
-- statement:
--   Assume Assumption 2.1: $U$ is a reflexive separable Banach space, $\xi\sim\mathcal N(0,\Sigma)$ is an $m$-dimensional Gaussian vector with nondegenerate covariance $\Sigma$, and $g:U\times\mathbb R^m\to\mathbb R$ is locally Lipschitzian with $g(u,\cdot)$ convex for every $u$. Let $\bar u\in U$ satisfy the Slater-type condition (10), $g(\bar u,0)<0$, and assume that the set $M=\{z\in\mathbb R^m\mid g(\bar u,z)\le0\}$ of (11) is bounded.
--
--   For $v\in\mathbb S^{m-1}$ let
--   $$
--   e(u,v)=\mu_\eta\big(\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}\big)
--   $$
--   be the radial probability function (13), where $\mu_\eta$ is the chi distribution with $m$ degrees of freedom. Then the functions $e(\cdot,v)$ are **uniformly locally Lipschitzian around $\bar u$**: there are a neighbourhood $N$ of $\bar u$ and a constant $K\ge0$, independent of $v$, such that
--   $$
--   |e(u,v)-e(u',v)|\le K\|u-u'\|\qquad\text{for all }u,u'\in N,\ v\in\mathbb S^{m-1}.
--   $$
--
--   This is the first assertion of Theorem 2.2 of the source, which cites [22, Theorem 5, Corollary 2, Proposition 6]. Together with the spherical-radial representation (14), it gives the local Lipschitz continuity of $\varphi$.
--
--   **Formalization Note.** This is the case of Theorem 2.2 in which $M$ is bounded; the other case (moderate growth (12)) is `theorem_2_2_e_lipschitz_moderate`. Conventions ($\mu_\eta$ as `chiLaw`, $\Sigma^{1/2}$ as `sqrtCov`, condition (12) as `ModerateGrowth`) are those of the Setting and Radial definition modules, exactly as in `ChanceStateCtrl.General.theorem_2_2_lipschitz`.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 5, Theorem 2.2 (first assertion), citing van Ackooij & Henrion [22, Thm 5, Cor 2, Prop 6]

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem theorem_2_2_e_lipschitz_bounded {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0) (hM : Bornology.IsBounded {z | g ub z ≤ 0}) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => radialProb Sigma g u v) t := by sorry

end ChanceStateCtrl.General
