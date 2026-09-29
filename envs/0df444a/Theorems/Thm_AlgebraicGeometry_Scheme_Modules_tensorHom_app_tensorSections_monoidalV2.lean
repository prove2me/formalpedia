-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/a2c29a5b-5c2a-5bc2-b10a-41d49b25c6dc
-- title:
--   Tensor product of morphisms on elementary tensor sections
-- statement:
--   Let $X$ be a scheme and let $L, L', M, M'$ be objects of `X.Modules`, the category of sheaves of $\mathcal O_X$-modules carrying the monoidal structure whose tensor product is the sheafification of the presheaf tensor product. Let $\varphi : L \to L'$ and $\psi : M \to M'$ be morphisms, let $U$ be an open subset of $X$, and let $s \in \Gamma(L,U)$ and $t \in \Gamma(M,U)$ be sections. Here `tensorSections s t` denotes the element of $\Gamma(L \otimes M, U)$ obtained by applying to the elementary tensor $s \otimes_{\Gamma(X,U)} t$ in $(L.\mathrm{val} \otimes M.\mathrm{val})(U)$ the $U$-component of `tensorSectionsHom`, that is of the unit of the sheafification adjunction at the presheaf tensor product $L.\mathrm{val} \otimes M.\mathrm{val}$ followed by the underlying-presheaf image of the comparison isomorphism `tensorIsoSheafify L M` between the sheafification of that presheaf tensor product and $L \otimes M$. The assertion is that the $U$-component of the morphism $\varphi \otimes_{\mathrm m} \psi : L \otimes M \to L' \otimes M'$ sends `tensorSections s t` to `tensorSections (φ.app U s) (ψ.app U t)`; in symbols, $(\varphi \otimes \psi)_U(s \otimes t) = \varphi_U(s) \otimes \psi_U(t)$ on elementary tensor sections.
--
--   This is the functoriality of the tensor product of sheaves of modules read on elementary tensor sections, the basic computational rule for the monoidal structure on `X.Modules`. It is used wherever sections of a tensor product must be pushed along a pair of morphisms, for instance in the treatment of invertible sheaves and their zero-schemes, in compatibilities of tensor powers with pullback, and in the descent arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections_monoidalV2
    {X : Scheme.{u}} {L L' M M' : X.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) (ψ.app U t) := by sorry
