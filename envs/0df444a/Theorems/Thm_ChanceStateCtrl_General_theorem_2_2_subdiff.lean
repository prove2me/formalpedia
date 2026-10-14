-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_theorem_2_2_subdiff
-- name    : ChanceStateCtrl.General.theorem_2_2_subdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:33.998953+00:00
-- url     : https://prove2.me/theorems/ff194423-c54a-419e-88b8-6042e7d2b09c
-- title:
--   Theorem 2.2 (15), (16), p. 5 — ∂^Cφ(ū) ⊆ ∫ ∂^C_u e(ū, v) dμ_ζ(v), with a singleton and equality under (16)
-- statement:
--   Assume Assumption 2.1, let $\bar u\in U$ satisfy (10), $g(\bar u,0)<0$, and either the moderate growth condition (12) at $\bar u$ or boundedness of $M=\{z\mid g(\bar u,z)\le0\}$. Then the Clarke subdifferential of $\varphi$ at $\bar u$ is estimated by the Aumann integral of the partial Clarke subdifferentials of $e$:
--   $$
--   \partial^C\varphi(\bar u)\subseteq\int_{\mathbb S^{m-1}}\partial^C_u e(\bar u,v)\,d\mu_\zeta(v).\tag{15}
--   $$
--   If moreover
--   $$
--   \mu_\zeta\{v\in\mathbb S^{m-1}\mid\#\partial^C_ue(\bar u,v)\ge2\}=0,\tag{16}
--   $$
--   then $\partial^C\varphi(\bar u)$ is a singleton and equality holds in (15).
--
--   The inclusion (15) is what makes the necessity part of the optimality condition (22) follow from (21).
--
--   **Formalization Note** $\partial^C_ue(\bar u,v)$ is the Clarke subdifferential of $u\mapsto e(u,v)$ at $\bar u$. "$\#\partial^C_ue(\bar u,v)\ge2$" is "$\partial^C_ue(\bar u,v)$ is not a subsingleton". The final consequence on the page, strict differentiability of $\varphi$ at $\bar u$ in the Hadamard sense, is not formalized. The paper states this theorem citing [22].
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 5, Theorem 2.2, (15) and (16); stated in this paper, citing [22, Theorem 5, Corollary 2 and Proposition 6]

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Definitions.Def_ChanceStateCtrl_General_Radial
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem theorem_2_2_subdiff {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (ub : U) (h10 : g ub 0 < 0)
    (h12 : ModerateGrowth g Sigma ub ∨ Bornology.IsBounded {z | g ub z ≤ 0}) :
    clarkeSubdiff (probFn P ξ g) ub ⊆
        aumann (sphereLaw m) (fun v => clarkeSubdiff (fun u => radialProb Sigma g u v) ub) ∧
      (sphereLaw m {v | ¬ (clarkeSubdiff (fun u => radialProb Sigma g u v) ub).Subsingleton} = 0 →
        (∃ x, clarkeSubdiff (probFn P ξ g) ub = {x}) ∧
          clarkeSubdiff (probFn P ξ g) ub =
            aumann (sphereLaw m) (fun v => clarkeSubdiff (fun u => radialProb Sigma g u v) ub)) := by sorry

end ChanceStateCtrl.General
