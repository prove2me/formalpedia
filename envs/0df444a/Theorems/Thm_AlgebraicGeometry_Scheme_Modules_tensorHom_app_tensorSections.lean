-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
-- name    : AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/57699fac-f5af-5cdd-bb74-faeedf4fd34a
-- title:
--   Tensor of morphisms acts on tensor of sections componentwise
-- statement:
--   Let $X$ be a scheme and let $L$, $L'$, $M$, $M'$ be sheaves of $\mathcal O_X$-modules, i.e. objects of `X.Modules`; let $\varphi : L \to L'$ and $\psi : M \to M'$ be morphisms of such sheaves, let $U$ be an open subset of $X$, and let $s \in \Gamma(L, U)$ and $t \in \Gamma(M, U)$ be sections over $U$. Here `tensorSections s t` denotes the element of $\Gamma(L \otimes M, U)$ obtained from the elementary tensor $s \otimes_{\Gamma(X,U)} t$ in the presheaf tensor product $(L.\mathrm{val} \otimes M.\mathrm{val})(U)$ by applying, at the open $U$, the morphism `tensorSectionsHom`, namely the unit of the sheafification adjunction for presheaves of modules over the structure sheaf of $X$ at $L.\mathrm{val} \otimes M.\mathrm{val}$ followed by the image under the forgetful functor to presheaves of the comparison isomorphism `tensorIsoSheafify` identifying the sheafification of the presheaf tensor product with the monoidal product $L \otimes M$ in `X.Modules`. The assertion is the equality, in $\Gamma(L' \otimes M', U)$, of the value of the section map of $\varphi \otimes_{\mathrm m} \psi$ over $U$ on `tensorSections s t` with `tensorSections` applied to $\varphi_U(s)$ and $\psi_U(t)$.
--
--   This is the basic functoriality of the tensor product of sheaves of modules on the level of sections: a tensor product of morphisms sends the section $s \otimes t$ to $\varphi_U(s) \otimes \psi_U(t)$. It is the computational tool used whenever tensor products of module sheaves on a scheme are manipulated through explicit sections, and is invoked in the treatment of invertible module sheaves and of ideal sheaves, for instance in identifying the tensor product of an invertible sheaf with a multiplicative translate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.lean

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

theorem AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} {L L' M M' : X.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) (ψ.app U t) := by sorry
