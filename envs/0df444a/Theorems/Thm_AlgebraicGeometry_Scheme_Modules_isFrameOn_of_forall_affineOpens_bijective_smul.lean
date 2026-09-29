-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul
-- name    : AlgebraicGeometry.Scheme.Modules.isFrameOn_of_forall_affineOpens_bijective_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/315cdbdc-e7e0-51a3-998a-540b309eea62
-- title:
--   Affine-local bijectivity of a↦ as gives a frame on U
-- statement:
--   Let $X$ be a scheme, let $N$ be an object of `X.Modules` (a sheaf of modules over the structure sheaf of $X$, with underlying presheaf of abelian groups `N.presheaf`), let $U$ be an open subset of $X$ and let $s \in \Gamma(N, U)$ be a section of $N$ over $U$. Assume that for every affine open $W$ of $X$ with $W \le U$ the map
--   $$\Gamma(X, W) \to \Gamma(N, W), \qquad a \mapsto a \cdot \bigl(s|_W\bigr),$$
--   where $s|_W$ denotes the image of $s$ under the restriction map of `N.presheaf` along the inclusion $W \le U$, is bijective. The conclusion is `Scheme.Modules.IsFrameOn s U`, which by definition says: for every open $W$ of $X$ equipped with a proof that $W \le U$ and a further proof that $W \le U$, the map $\Gamma(X, W) \to \Gamma(N, W)$, $g \mapsto g \cdot (s|_W)$, is bijective. Thus bijectivity of multiplication by $s$ on affine opens contained in $U$ is upgraded to bijectivity on all opens contained in $U$. No quasi-coherence, finiteness or separatedness hypothesis occurs.
--
--   This is the affine-local criterion for a section to trivialise a sheaf of modules: it says that the $\mathcal O_X$-linear map $\mathcal O_U \to N|_U$ given by multiplication by $s$ is an isomorphism as soon as it is so over the affine opens of $U$. It is used in the study of relative group laws and of abelian schemes with good reduction, where local trivialising sections of invertible sheaves are produced on affine opens and then have to be recognised as frames over arbitrary opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_of_forall_affineOpens_bijective_smul.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.isFrameOn_of_forall_affineOpens_bijective_smul
    {X : Scheme.{u}} (N : X.Modules) (U : X.Opens) (s : Γ(N, U))
    (h : ∀ (W : X.affineOpens) (hW : W.1 ≤ U),
      Function.Bijective (fun a : Γ(X, W.1) => a • (N.presheaf.map (homOfLE hW).op s : Γ(N, W.1)))) :
    Scheme.Modules.IsFrameOn s U := by sorry
