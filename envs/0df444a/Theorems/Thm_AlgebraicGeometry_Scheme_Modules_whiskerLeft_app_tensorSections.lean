-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections
-- name    : AlgebraicGeometry.Scheme.Modules.whiskerLeft_app_tensorSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/bddc8cc0-b17d-5cf7-a5af-e9bbc4206201
-- title:
--   Left whiskering on sections: (L ⊗ ψ)(s ⊗ t) = s ⊗ ψ(t)
-- statement:
--   Let $X$ be a scheme, let $L$ be a sheaf of $\mathcal{O}_X$-modules on $X$ (an object of `X.Modules`), let $M$, $M'$ be two further such sheaves and let $\psi \colon M \to M'$ be a morphism of sheaves of $\mathcal{O}_X$-modules. Let $U$ be an open subset of $X$, and let $s \in \Gamma(L, U)$ and $t \in \Gamma(M, U)$ be sections over $U$ of $L$ and of $M$. Here `tensorSections s t` denotes the element of $\Gamma(L \otimes M, U)$ obtained from the elementary tensor $s \otimes_{\Gamma(X,U)} t$ in the presheaf tensor product $(L.\mathrm{val} \otimes M.\mathrm{val})(U)$ by applying, at the object $U$, the morphism `tensorSectionsHom`, i.e. the unit of the sheafification adjunction for presheaves of modules followed by the canonical isomorphism identifying the sheafification of the presheaf tensor product with the monoidal product $L \otimes M$; and $\rhd$-whiskering $L \lhd \psi$ is the left whiskering $L \otimes \psi \colon L \otimes M \to L \otimes M'$ of the monoidal structure. The assertion is that the map on sections over $U$ induced by $L \lhd \psi$ sends `tensorSections s t` to `tensorSections s (ψ.app U t)`, an equality in $\Gamma(L \otimes M', U)$.
--
--   This is the compatibility of elementary tensors of sections with the functoriality of the tensor product in the second variable, in the whiskered form in which Mathlib's monoidal API phrases it; it is the special case $\varphi = \mathrm{id}_L$ of $(\varphi \otimes \psi)(s \otimes t) = \varphi(s) \otimes \psi(t)$. It is used in the computations with invertible modules and relative Picard groups, for instance in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections.lean

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

theorem AlgebraicGeometry.Scheme.Modules.whiskerLeft_app_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) {M M' : X.Modules} (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ◁ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections s (ψ.app U t) := by sorry
