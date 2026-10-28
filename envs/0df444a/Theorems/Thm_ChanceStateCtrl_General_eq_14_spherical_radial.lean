-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_eq_14_spherical_radial
-- name    : ChanceStateCtrl.General.eq_14_spherical_radial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:44.617129+00:00
-- url     : https://prove2.me/theorems/0902b306-b729-467b-a51b-93e947018b80
-- title:
--   (14), p. 5 — spherical-radial representation φ(u) = ∫_{S^{m−1}} e(u, v) dμ_ζ(v)
-- statement:
--   Assume Assumption 2.1. Then for every $u\in U$ the probability function is the spherical integral of the radial probability function:
--   $$
--   \varphi(u)=\int_{\mathbb S^{m-1}}e(u,v)\,d\mu_\zeta(v)\qquad(u\in U),\tag{14}
--   $$
--   where $e(u,v)=\mu_\eta\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}$, $\mu_\eta$ is the chi distribution with $m$ degrees of freedom and $\mu_\zeta$ the uniform distribution on $\mathbb S^{m-1}$.
--
--   This is the spherical-radial decomposition of the Gaussian vector $\xi$; it is the representation on which the subdifferential formulas (15) and Theorem 2.4 rest.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 5, (14)

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem eq_14_spherical_radial {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g) :
    ∀ u : U, probFn P ξ g u = ∫ v, radialProb Sigma g u v ∂(sphereLaw m) := by sorry

end ChanceStateCtrl.General
