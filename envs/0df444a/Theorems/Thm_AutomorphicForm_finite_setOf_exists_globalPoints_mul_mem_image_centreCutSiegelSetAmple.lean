-- Prove2me | Theorems.Thm_AutomorphicForm_finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple
-- name    : AutomorphicForm.finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/025604e2-eb21-5966-ab5b-4afd1a25bb2f
-- title:
--   Siegel finiteness for ample centre-cut Siegel sets
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\kappa$ be real numbers with $c>0$ and $d_1>0$, and let $x$ be an element of $\mathrm{GL}_2$ of the adele ring of $F$ such that for every infinite place $w$ of $F$ the image $\mathrm{archComponent}_w(\mathrm{glArch}(x))$ of $x$ in $\mathrm{GL}_2(F_w)$ lies in `rowIsometrySubgroup`, i.e. is a row isometry: its determinant has norm $1$ and the assignment $(\xi,\eta)\mapsto(\xi k_{00}+\eta k_{10},\ \xi k_{01}+\eta k_{11})$ preserves $\|\xi\|^2+\|\eta\|^2$. Write $\mathfrak S=\mathrm{centreCutSiegelSetAmple}\,F\,c\,u\,d_1\,d_2\,\kappa$ for the set of $g\in\mathrm{GL}_2(\mathbb A_F)$ whose finite part `glFin` lies in `finiteIntegralGL2`, whose archimedean local heights satisfy $c\le \mathrm{localHeight}(g_w)$ for all infinite places $w$, where $\mathrm{localHeight}(h)=\|\det h\|/\mathrm{rowNormSq}(h)$, whose window quantities satisfy $\mathrm{xWindowSq}(g_w)\le u^2$, whose archimedean determinant norms $\mathrm{archDetNorm}_w(g)$ lie in $[d_1,d_2]$, and which in addition satisfy the ampleness clause $\mathrm{localHeight}(g_w)\le\kappa\,\mathrm{localHeight}(g_{w'})$ for all pairs of infinite places $w,w'$. Then the set of $\gamma\in\mathrm{GL}_2(F)$ for which there exists $s\in\mathfrak S$ with $\mathrm{globalPoints}(\gamma)\cdot s\in\mathfrak S\cdot x$ is finite.
--
--   This is the Siegel property for the ample centre-cut Siegel sets used here: the positive height floor $c$, the positive determinant floor $d_1$ and the $\kappa$-comparability of archimedean local heights make the relevant region compact enough that only finitely many rational points can move $\mathfrak S$ into the right translate $\mathfrak S x$. It is used to obtain uniform bounds on the number of such $\gamma$ over finite unions of such sets, and through these in the construction of genuine realisations of weight-one automorphic forms in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ κ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (x : AdelicGL2 (𝓞 F) F)
    (hx : ∀ w : InfinitePlace F,
      archComponent F w (glArch (𝓞 F) F x) ∈ rowIsometrySubgroup (w.Completion)) :
    Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ,
        globalPoints (𝓞 F) F γ * s ∈ (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ} := by sorry
