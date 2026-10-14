-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_lemma_2_3
-- name    : ChanceStateCtrl.General.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:40.674001+00:00
-- url     : https://prove2.me/theorems/2d296121-8ea2-416e-bffb-6854ac94fc29
-- title:
--   Lemma 2.3, p. 6 — for jointly convex g, (10) and M bounded, −e(·, v) is Clarke regular on N(ū)
-- statement:
--   Assume Assumption 2.1, and let $g$ in addition be jointly convex in both variables. Let $\bar u\in U$ satisfy (10), $g(\bar u,0)<0$, and let the set $M=\{z\mid g(\bar u,z)\le0\}$ of (11) be bounded. Let $\mathcal N(\bar u)$ be an open neighbourhood of $\bar u$ with $g(u,0)<0$ for all $u\in\mathcal N(\bar u)$. Then for each $v\in\mathbb S^{m-1}$ the function
--   $$
--   u\mapsto-e(u,v)
--   $$
--   is Clarke regular at every point of $\mathcal N(\bar u)$.
--
--   Clarke regularity of the integrand is the hypothesis under which Clarke's theorem on integral functionals gives an equality, which is how Theorem 2.4 sharpens (15).
--
--   **Formalization Note** The page introduces $\mathcal N(\bar u)$ as "some neighborhood" with $g(u,0)<0$ on it; the statement is made for every open such neighbourhood. Clarke regularity includes local Lipschitz continuity (the page defines regularity for locally Lipschitzian functions).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 6, Lemma 2.3

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem lemma_2_3 {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (hg_jc : ConvexOn ℝ Set.univ (Function.uncurry g))
    (ub : U) (h10 : g ub 0 < 0) (hM : Bornology.IsBounded {z | g ub z ≤ 0})
    (N : Set U) (hN_open : IsOpen N) (hub : ub ∈ N) (hN : ∀ u ∈ N, g u 0 < 0) :
    ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1, ∀ u ∈ N,
      IsClarkeRegularAt (fun w => -radialProb Sigma g w v) u := by sorry

end ChanceStateCtrl.General
