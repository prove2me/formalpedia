-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_lipschitz
-- name    : ChanceStateCtrl.General.theorem_2_2_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:34.823001+00:00
-- url     : https://prove2.me/theorems/e80ba5c3-dd46-42e8-93fe-dad6ce007414
-- title:
--   Theorem 2.2 (Lipschitz part), p. 5 — e(·, v) uniformly locally Lipschitz around ū and φ locally Lipschitz around ū
-- statement:
--   Assume Assumption 2.1: $U$ is a reflexive separable Banach space, $\xi\sim\mathcal N(0,\Sigma)$ is an $m$-dimensional Gaussian vector with nondegenerate $\Sigma$, and $g:U\times\mathbb R^m\to\mathbb R$ is locally Lipschitzian with $g(u,\cdot)$ convex for every $u$. Let $\bar u\in U$ satisfy the Slater-type condition (10),
--   $$
--   g(\bar u,0)<0,
--   $$
--   and either the moderate growth condition (12) at $\bar u$ or boundedness of the set $M=\{z\in\mathbb R^m\mid g(\bar u,z)\le0\}$ of (11). Then
--
--   1. the partial radial probability functions $e(\cdot,v)$, $v\in\mathbb S^{m-1}$, are uniformly locally Lipschitzian around $\bar u$: there are one neighbourhood of $\bar u$ and one constant $K$, independent of $v$, such that every $e(\cdot,v)$ is $K$-Lipschitz on that neighbourhood;
--   2. the probability function $\varphi(u)=\mathbb P(g(u,\xi)\le0)$ is locally Lipschitzian around $\bar u$.
--
--   This is the regularity result that makes Clarke's subdifferential of $\varphi$ available at $\bar u$; it is the first step of the proof of Proposition 2.6.
--
--   **Formalization Note** The paper states this theorem citing [22] (Theorem 5, Corollary 2 and Proposition 6). The subdifferential statements of Theorem 2.2, (15) and (16), are a separate item.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 5, Theorem 2.2 (first two sentences); stated in this paper, citing [22, Theorem 5, Corollary 2 and Proposition 6]

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem theorem_2_2_lipschitz {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0)
    (h12 : ModerateGrowth g Sigma ub ∨ Bornology.IsBounded {z | g ub z ≤ 0}) :
    (∃ K : NNReal, ∃ t ∈ 𝓝 ub, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
        LipschitzOnWith K (fun u => radialProb Sigma g u v) t) ∧
      LocLipAt (probFn P ξ g) ub := by sorry

end ChanceStateCtrl.General
