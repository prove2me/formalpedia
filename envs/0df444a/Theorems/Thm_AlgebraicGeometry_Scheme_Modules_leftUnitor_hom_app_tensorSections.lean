-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections
-- name    : AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tensorSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/3f0bf8df-67bd-5e64-a502-7afa8d199d8d
-- title:
--   Left unitor on sections: λ_N(g⊗ n)=g· n
-- statement:
--   Let $X$ be a scheme, let $N$ be a sheaf of $\mathcal O_X$-modules on $X$ (an object of `X.Modules`), let $U$ be an open subset of $X$, and let $g \in \Gamma(X,U)$ and $n \in \Gamma(N,U)$ be sections over $U$ of the structure sheaf and of $N$ respectively. Here $g$ is read as a section over $U$ of the monoidal unit $\mathbb 1$ of `X.Modules`, and `tensorSections` applied to $g$ and $n$ is the section of $\mathbb 1 \otimes N$ over $U$ obtained by forming the elementary tensor $g \otimes_{\Gamma(X,U)} n$ in the presheaf-level tensor product and then applying the component at $U$ of `tensorSectionsHom`, that is, of the unit of the sheafification adjunction for modules followed by the image under the forgetful functor to presheaves of modules of the isomorphism `tensorIsoSheafify` identifying the sheafified presheaf tensor product with the tensor product of sheaves of modules. The assertion is that the component at $U$ of the left unitor isomorphism $\lambda_N \colon \mathbb 1 \otimes N \xrightarrow{\ \sim\ } N$ sends this section to $g \cdot n$, the action of $g \in \Gamma(X,U)$ on $n \in \Gamma(N,U)$.
--
--   This is the sections-level description of the left unitor of the monoidal structure on sheaves of modules on a scheme, the statement that $\mathcal O_X \otimes_{\mathcal O_X} \mathcal N \cong \mathcal N$ is given on sections by $g \otimes n \mapsto g n$. It is used wherever invertible modules and ideal sheaves are manipulated through explicit sections, for instance in the treatment of invertible modules and relative Picard groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n := by sorry
