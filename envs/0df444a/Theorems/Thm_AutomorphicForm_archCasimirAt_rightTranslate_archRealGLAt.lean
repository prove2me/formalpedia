-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt
-- name    : AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/86b4fed1-b27b-5fdd-b16d-8630dcc5fb8a
-- title:
--   Casimir at a real place commutes with right translation by GL₂(ℝ)
-- statement:
--   Let $K$ be a number field and $w$ a real infinite place of $K$, with $hw$ the witness that $w$ is real. Write $\mathrm{GL}_2(\mathbb{A}_K)$ for `AdelicGL2 (𝓞 K) K`, and for $m \in \mathrm{GL}(2,\mathbb{R})$ let `archRealGLAt hw m` be its image in $\mathrm{GL}_2(\mathbb{A}_K)$ under the monoid homomorphism obtained from the isomorphism of $w$'s completion with $\mathbb{R}$ followed by the archimedean inclusion at $w$. Let $x \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and satisfy `IsArchSmoothAt hw x`, i.e. for every $g$ the function $e \mapsto x(g \cdot \mathtt{archRealLiftAt } hw\, e)$ on real $2\times 2$ arrays is $C^\infty$ on the open set where $\det e \neq 0$; assume moreover that for each direction $d \in \{H, E, F^-\}$ the derivative `archDerivAt hw d x`, given by $g \mapsto \frac{d}{dt}\big|_{t=0} x(g \cdot \mathtt{archFlowAt } hw\, d\, t)$ along the corresponding one-parameter family placed at $w$, is continuous, and that all second derivatives `archDerivAt hw d (archDerivAt hw d' x)` are continuous. Then for every $m \in \mathrm{GL}(2,\mathbb{R})$ the right translate $g \mapsto x(g \cdot \mathtt{archRealGLAt } hw\, m)$ again satisfies `IsArchSmoothAt hw`, has continuous first and second archimedean derivatives in all directions, and satisfies $\Omega_w(R_m x) = R_m(\Omega_w x)$, where $\Omega_w \varphi = -\big(\tfrac14 D_H D_H \varphi - \tfrac12 D_H \varphi + D_E D_{F^-} \varphi\big)$ is `archCasimirAt hw`.
--
--   This is the $\mathrm{Ad}$-invariance (centrality) of the Casimir element of $U(\mathfrak{gl}_2(\mathbb{R}))$, expressed as commutation of the Casimir operator at a real place with right translation by an element of $\mathrm{GL}(2,\mathbb{R})$ placed at that place, together with the preservation of the relevant smoothness and continuity conditions. It is used in the construction of the Casimir action on spaces of automorphic forms and on test functions, in particular by the statements combining the Casimir with right convolution for archimedean-bi-finite data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean

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

theorem AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ m : GL (Fin 2) ℝ,
        IsArchSmoothAt hw (rightTranslate K (archRealGLAt hw m) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (archRealGLAt hw m) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (archRealGLAt hw m) x)))) ∧
        archCasimirAt hw (rightTranslate K (archRealGLAt hw m) x) =
          rightTranslate K (archRealGLAt hw m) (archCasimirAt hw x) := by sorry
