-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
-- name    : AutomorphicForm.exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/899f8d3b-6726-5818-a066-0e25db0bc658
-- title:
--   Unit translation into an ample centre-cut Siegel set
-- statement:
--   Let $K$ be a number field. The assertion is that there exist real constants $\kappa, R, \theta$ with $\kappa \ge 1$ and $\theta > 0$ — depending on $K$ alone, and in particular chosen before the Siegel parameters — such that for all reals $c, u, d_1, d_2$ and every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ lying in `centreCutSiegelSet K c u d₁ d₂`, i.e. such that the finite component `glFin` of $g$ lies in the subgroup `finiteIntegralGL2` ($=$ `finiteLevelZero` at level $\top$) and, at every infinite place $w$ of $K$, the archimedean component $g_w \in \mathrm{GL}_2(K_w)$ obtained from `glArch` followed by `archComponent` satisfies $c \le H_w(g) := |\det g_w| / \mathrm{rowNormSq}(g_w)$, satisfies $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w) - H_w(g)^2 \le u^2$, and has $\|\det g_w\| \in [d_1, d_2]$, there is a $\delta \in \mathrm{GL}_2(K)$ whose underlying matrix is $\begin{pmatrix} \varepsilon & \beta \\ 0 & \varepsilon^{-1}\end{pmatrix}$ for some unit $\varepsilon \in \mathcal{O}_K^\times$ and some $\beta \in \mathcal{O}_K$ (images in $K$), such that the product of the image of $\delta$ under `globalPoints` (the entrywise diagonal embedding $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A}_K)$) with $g$ lies in `centreCutSiegelSetAmple K (θ * c) R d₁ d₂ κ`: it again has integral finite component, local heights $\ge \theta c$, windows $\le R^2$ and determinant norms in $[d_1, d_2]$ at every infinite place, and moreover $H_w \le \kappa \, H_{w'}$ for every pair of infinite places $w, w'$. No positivity or sign hypotheses are imposed on $c, u, d_1, d_2$, and $R$ is not asserted to be positive.
--
--   This is the pointwise form of reduction theory with units for $\mathrm{GL}_2$ over a number field: an arbitrary point of a centre-cut Siegel set is moved by an integral upper-triangular matrix of determinant one into a Siegel set whose local heights are comparable across the infinite places, with constants independent of the defining parameters. It is used in the estimation of unipotent contributions to cuspidal terms, being cited by [`UnipotentTermCuspBound.exists_forall_setLIntegral_tsum_setLIntegral_enorm_mul_tsum_tsum_enorm_sub_ne_top`](thm.html#UnipotentTermCuspBound.exists_forall_setLIntegral_tsum_setLIntegral_enorm_mul_tsum_tsum_enorm_sub_ne_top); the choice of $\varepsilon$ rests on the Dirichlet-type balancing statement [`NumberField.Units.exists_forall_abs_two_mul_log_add_log_sub_div_le`](thm.html#NumberField.Units.exists_forall_abs_two_mul_log_add_log_sub_div_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_mem_centreCutSiegelSet_globalPoints_mul_mem_centreCutSiegelSetAmple
    (K : Type) [Field K] [NumberField K] :
    ∃ κ R θ : ℝ, 1 ≤ κ ∧ 0 < θ ∧
      ∀ (c u d₁ d₂ : ℝ), ∀ g ∈ centreCutSiegelSet K c u d₁ d₂,
        ∃ δ : GL (Fin 2) K,
          (∃ (ε : (𝓞 K)ˣ) (β : 𝓞 K),
              (δ : Matrix (Fin 2) (Fin 2) K) =
                !![((ε : 𝓞 K) : K), ((β : 𝓞 K) : K); 0, (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)]) ∧
          globalPoints (𝓞 K) K δ * g ∈ centreCutSiegelSetAmple K (θ * c) R d₁ d₂ κ := by sorry
