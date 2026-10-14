-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_prekopa_logconcave
-- name    : ChanceStateCtrl.General.prekopa_logconcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:44.387833+00:00
-- url     : https://prove2.me/theorems/ab50b33b-7b6c-4c71-95a2-1d99805171e0
-- title:
--   p. 7, the statement preceding Lemma 2.5 (Prékopa) — jointly quasi-convex g and log-concave density give log-concave φ
-- statement:
--   Let $U$ be a real normed space, $(\Omega,\mathcal F,\mathbb P)$ a probability space and $\xi:\Omega\to\mathbb R^m$ a random vector whose law has a log-concave density $\varrho\ge0$ with respect to Lebesgue measure, i.e.
--   $$
--   \varrho(z)^t\,\varrho(w)^{1-t}\le\varrho(tz+(1-t)w)\qquad\forall z,w\in\mathbb R^m,\ t\in[0,1].
--   $$
--   Let $g:U\times\mathbb R^m\to\mathbb R$ be locally Lipschitzian and quasi-convex jointly in both variables. Then the probability function $\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le0)$ is log-concave:
--   $$
--   \varphi(u)^t\,\varphi(w)^{1-t}\le\varphi(tu+(1-t)w)\qquad\forall u,w\in U,\ t\in[0,1],
--   $$
--   that is, $\log\varphi$ is concave under the convention $\log0=-\infty$.
--
--   Since a nondegenerate Gaussian density is log-concave, this is what makes the reformulation (20) of the chance-constrained problem (9) convex.
--
--   **Formalization Note** The page writes "under the convention $\log 0:=\infty$"; concavity of $\log\varphi$ requires $\log0=-\infty$, and the multiplicative form above (with $0^0=1$) is exactly log-concavity under that convention. Local Lipschitz continuity of $g$ is the standing Assumption 2.1(iv) of the section; it also makes the events $\{g(u,\xi)\le0\}$ measurable. The paper states this result citing [13, Proposition 4] and [41, Theorem 10.2.1].
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 7, the statement preceding Lemma 2.5; stated in this paper, citing [13, Proposition 4] and [41, Theorem 10.2.1]

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem prekopa_logconcave {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U]
    [NormedSpace ℝ U] {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (dens : EuclideanSpace ℝ (Fin m) → ℝ) (hdens_nonneg : ∀ z, 0 ≤ dens z)
    (hdens_meas : Measurable dens)
    (hlaw : P.map ξ = volume.withDensity (fun z => ENNReal.ofReal (dens z)))
    (hdens_logconcave : ∀ z w : EuclideanSpace ℝ (Fin m), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dens z ^ t * dens w ^ (1 - t) ≤ dens (t • z + (1 - t) • w))
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hg_lip : LocallyLipschitz (Function.uncurry g))
    (hg_qc : QuasiconvexOn ℝ Set.univ (Function.uncurry g)) :
    ∀ u w : U, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      probFn P ξ g u ^ t * probFn P ξ g w ^ (1 - t) ≤ probFn P ξ g (t • u + (1 - t) • w) := by sorry

end ChanceStateCtrl.General
