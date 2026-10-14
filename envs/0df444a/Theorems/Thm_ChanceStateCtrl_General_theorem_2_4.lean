-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_theorem_2_4
-- name    : ChanceStateCtrl.General.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:40.919743+00:00
-- url     : https://prove2.me/theorems/962ce616-2789-4c07-8131-abdacf90ea2b
-- title:
--   Theorem 2.4, p. 7 — under Lemma 2.3's assumptions ∂^Cφ(ū) = ∫_{S^{m−1}} ∂^C_u e(ū, v) dμ_ζ(v)
-- statement:
--   Assume Assumption 2.1, let $g$ be jointly convex in both variables, and let $\bar u\in U$ satisfy (10), $g(\bar u,0)<0$, with $M=\{z\mid g(\bar u,z)\le0\}$ bounded. Then the Clarke subdifferential of the probability function is exactly the Aumann integral of the partial Clarke subdifferentials of the radial probability function:
--   $$
--   \partial^C\varphi(\bar u)=\int_{\mathbb S^{m-1}}\partial^C_ue(\bar u,v)\,d\mu_\zeta(v).
--   $$
--
--   The exact formula is what makes the condition (22) sufficient for optimality when $M$ is bounded, without the differentiability condition (16).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 7, Theorem 2.4

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem theorem_2_4 {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (hg_jc : ConvexOn ℝ Set.univ (Function.uncurry g))
    (ub : U) (h10 : g ub 0 < 0) (hM : Bornology.IsBounded {z | g ub z ≤ 0}) :
    clarkeSubdiff (probFn P ξ g) ub =
      aumann (sphereLaw m) (fun v => clarkeSubdiff (fun u => radialProb Sigma g u v) ub) := by sorry

end ChanceStateCtrl.General
