-- Prove2me | Theorems.Thm_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt
-- name    : AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/da524b2a-2774-561f-84bc-a46aff30aa0d
-- title:
--   Left and right Casimir agree at a real place
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with $hw$ a witness that $w$ is real, and let $\theta$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $K$ (the general linear group of degree $2$ over the adele ring of $\mathcal{O}_K$ in $K$). Assume $\theta$ satisfies `IsArchSmoothAt hw`, that is: for every adelic point $g$ the function $e \mapsto \theta(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$ on $2 \times 2$ real matrices is $C^\infty$ on the open set where $\det(e) \neq 0$, where $\mathrm{archRealLiftAt}$ sends an invertible real matrix to its image in the adelic group under the inclusion at $w$ coming from the identification of the completion at the real place $w$ with $\mathbb{R}$ (and sends singular $e$ to $1$). Define, for each direction $d \in \{H, E, F^{-}\}$ and each function $\gamma$, the left derivative $(L_d\gamma)(y) = \frac{d}{dt}\big|_{t=0}\gamma(\mathrm{archFlowAt}\,hw\,d\,(-t) \cdot y)$, where $\mathrm{archFlowAt}\,hw\,d\,t$ is the image at $w$ of the one-parameter subgroup of $\mathrm{GL}_2(\mathbb{R})$ attached to $d$ (the split torus for $H$, the upper unipotent for $E$, the lower unipotent for $F^{-}$). The conclusion is that for every adelic point $y$,
--   $$-\Big(\tfrac14 L_H L_H\theta - \tfrac12 L_H\theta + L_E L_{F^{-}}\theta\Big)(y) = (\mathrm{archCasimirAt}\,hw\,\theta)(y),$$
--   where the right-hand side is the same combination $-\big(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_{F^{-}}\big)\theta$ formed from the right derivatives $(D_d\varphi)(g) = \frac{d}{dt}\big|_{t=0}\varphi(g \cdot \mathrm{archFlowAt}\,hw\,d\,t)$.
--
--   This is the centrality ($\mathrm{Ad}$-invariance) of the Casimir element of $U(\mathfrak{gl}_2(\mathbb{R}))$ in the present concrete form: the Casimir built from left flows at the real place $w$ acts on functions smooth at $w$ exactly as the Casimir built from right flows. It is used to transfer the Casimir operator across right translations and convolutions, and is cited in the results on the behaviour of `archCasimirAt` under right convolution with factorisable test functions and on archimedean finiteness of such convolutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAt hw θ) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    ∀ y : AdelicGL2 (𝓞 K) K,
      -((1 / 4 : ℂ) * L .H (L .H θ) y - (1 / 2 : ℂ) * L .H θ y + L .E (L .Fm θ) y) = archCasimirAt hw θ y := by sorry
