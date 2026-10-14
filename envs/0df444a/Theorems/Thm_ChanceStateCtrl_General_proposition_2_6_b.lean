-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_proposition_2_6_b
-- name    : ChanceStateCtrl.General.proposition_2_6_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:48.511892+00:00
-- url     : https://prove2.me/theorems/f79748dd-6b82-43eb-833f-b53315f3d49b
-- title:
--   Proposition 2.6 (22), p. 8 — (22) with the spherical integral of ∂^C_u e is necessary, and sufficient under (16) or M bounded
-- statement:
--   Under the hypotheses of Proposition 2.6 (21) — $U$ reflexive separable Banach, $F$ convex and Fréchet differentiable, $\xi\sim\mathcal N(0,\Sigma)$ nondegenerate, $g$ locally Lipschitzian and jointly convex, a generalized Slater point $\hat u$ with $\varphi(\hat u)>p$, $p\in(0,1]$, and $u^*$ feasible with $g(u^*,0)<0$ and either (12) at $u^*$ or $M=\{z\mid g(u^*,z)\le0\}$ bounded — the following hold.
--
--   1. **Necessity.** If $u^*$ is a solution of (9), there is $\lambda\ge0$ with
--   $$
--   DF(u^*)\in\lambda\int_{\mathbb S^{m-1}}\partial^C_ue(u^*,v)\,d\mu_\zeta(v),\qquad\varphi(u^*)\ge p,\qquad\lambda(\varphi(u^*)-p)=0.\tag{22}
--   $$
--   2. **Sufficiency.** If moreover (16) holds at $u^*$, $\mu_\zeta\{v\mid\#\partial^C_ue(u^*,v)\ge2\}=0$, or $M$ is bounded, then (22) implies that $u^*$ is a solution of (9).
--
--   Condition (22) replaces the abstract Clarke subdifferential of $\varphi$ by an integral of subdifferentials of the explicit radial function $e$, which is the form the paper evaluates in its PDE application.
--
--   **Formalization Note** As in (21), "$DF(u^*)\in\lambda\int\cdots$" is written with an element $x^*$ of the Aumann integral and $DF(u^*)=\lambda x^*$. "$\#\partial^C_ue(u^*,v)\ge2$" is "not a subsingleton".
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 8, Proposition 2.6, second statement (22)

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem proposition_2_6_b {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (hg_jc : ConvexOn ℝ Set.univ (Function.uncurry g))
    (F : U → ℝ) (hF_convex : ConvexOn ℝ Set.univ F) (hF_diff : Differentiable ℝ F)
    (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) (hslater : ∃ uh : U, p < probFn P ξ g uh)
    (us : U) (hfeas : p ≤ probFn P ξ g us) (h10 : g us 0 < 0)
    (h12 : ModerateGrowth g Sigma us ∨ Bornology.IsBounded {z | g us z ≤ 0}) :
    (IsSolution {u | p ≤ probFn P ξ g u} F us →
      ∃ lam : ℝ, 0 ≤ lam ∧
        (∃ x ∈ aumann (sphereLaw m) (fun v => clarkeSubdiff (fun u => radialProb Sigma g u v) us),
          fderiv ℝ F us = lam • x) ∧
        p ≤ probFn P ξ g us ∧ lam * (probFn P ξ g us - p) = 0) ∧
    ((sphereLaw m {v | ¬ (clarkeSubdiff (fun u => radialProb Sigma g u v) us).Subsingleton} = 0 ∨
        Bornology.IsBounded {z | g us z ≤ 0}) →
      (∃ lam : ℝ, 0 ≤ lam ∧
        (∃ x ∈ aumann (sphereLaw m) (fun v => clarkeSubdiff (fun u => radialProb Sigma g u v) us),
          fderiv ℝ F us = lam • x) ∧
        p ≤ probFn P ξ g us ∧ lam * (probFn P ξ g us - p) = 0) →
      IsSolution {u | p ≤ probFn P ξ g u} F us) := by sorry

end ChanceStateCtrl.General
