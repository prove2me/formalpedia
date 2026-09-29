-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections
-- name    : AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/0bfd7f14-1cd6-5482-aa19-d1cc091fa27d
-- title:
--   Right unitor on sections: ρ_N(n⊗ g)=g· n
-- statement:
--   Let $X$ be a scheme, let $N$ be a sheaf of $\mathcal{O}_X$-modules (an object of `X.Modules`), let $U$ be an open of $X$, and let $n \in \Gamma(N,U)$ and $g \in \Gamma(X,U) = \mathcal{O}_X(U)$, the latter being used directly as a section over $U$ of the monoidal unit $\mathbb{1}$ of `X.Modules`. Write `tensorSections n g` for the section of $N \otimes \mathbb{1}$ over $U$ obtained as follows: form the elementary tensor $n \otimes_{\Gamma(X,U)} g$ in the value over $U$ of the presheaf-level tensor product of the underlying presheaves of modules, and apply to it the component at $U$ of `tensorSectionsHom`, namely the unit of the sheafification adjunction for presheaves of modules over $\mathcal{O}_X$ followed by the image, under the forgetful functor from sheaves to presheaves of modules, of the isomorphism `tensorIsoSheafify` identifying the sheafification of the presheaf tensor product with the tensor product $N \otimes \mathbb{1}$ of sheaves. The assertion is that the component over $U$ of the right unitor $\rho_N \colon N \otimes \mathbb{1} \xrightarrow{\ \sim\ } N$ sends this section to $g \cdot n \in \Gamma(N,U)$.
--
--   This is the explicit description, on sections over an open set, of the right unitor of the monoidal structure on quasi-coherent-free sheaves of modules on a scheme: the canonical isomorphism $N \otimes_{\mathcal{O}_X} \mathcal{O}_X \cong N$ acts on elementary tensors by scalar multiplication (in particular $\rho_N(n \otimes 1) = n$). It is used in the computations with invertible modules and relative Picard groups, for instance in the criteria for a map of modules to be an isomorphism in terms of pullbacks of sections and determinants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections.lean

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

theorem AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (n : Γ(N, U)) (g : Γ(X, U)) :
    (ρ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := N) (M := 𝟙_ X.Modules) n g) = g • n := by sorry
