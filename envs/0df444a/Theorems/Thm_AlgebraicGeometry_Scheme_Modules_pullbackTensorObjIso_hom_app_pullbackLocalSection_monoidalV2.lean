-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/ad16f0d7-8022-5252-9b0f-a8f41c923646
-- title:
--   Pullback of a tensor product of sections
-- statement:
--   Let $\varphi \colon X \to Y$ be a morphism of schemes, let $L, M$ be sheaves of modules on $Y$, let $U$ be an open subset of $Y$, and let $s \in \Gamma(L, U)$ and $t \in \Gamma(M, U)$. Write $\varphi^{*}$ for `Modules.pullback φ` and, for a section $u$ over $U$, let $\varphi^{*}u \in \Gamma(\varphi^{*}(-), \varphi^{-1}U)$ denote `pullbackLocalSection`, that is, the image of $u$ under the component at $U$ of the unit of the adjunction $\varphi^{*} \dashv \varphi_{*}$ evaluated at the relevant module. For sections $s, t$ over a common open $U$ of modules on a fixed scheme, `tensorSections s t` $\in \Gamma(L \otimes M, U)$ is the image of $s \otimes_{\Gamma(X,U)} t$, taken in the presheaf tensor product $(L.\mathrm{val} \otimes M.\mathrm{val})(U)$, under the component at $U$ of the unit of sheafification followed by the comparison of $L \otimes M$ with the sheafification of the presheaf tensor product. Let `pullbackTensorObjIso` be the isomorphism $\varphi^{*}(L \otimes M) \cong \varphi^{*}L \otimes \varphi^{*}M$ given by the inverse of the monoidal-structure isomorphism $\mu$ of the functor $\varphi^{*}$. The assertion is that evaluating this isomorphism at the open $\varphi^{-1}U$ and applying it to $\varphi^{*}(s \otimes t)$ yields $\varphi^{*}s \otimes \varphi^{*}t$ in $\Gamma(\varphi^{*}L \otimes \varphi^{*}M, \varphi^{-1}U)$.
--
--   This is the compatibility of inverse image with tensor products of sections: the monoidal comparison isomorphism for $\varphi^{*}$ sends the pullback of a decomposable section to the tensor product of the pullbacks. It is the computational form in which the monoidal structure on pullback of sheaves of modules is used further on, for instance in the treatment of tensor powers of invertible modules and in the compatibility of pullback along a composite with tensor products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso_hom_app_pullbackLocalSection_monoidalV2
    {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⟶ Y) {L M : Y.Modules} {U : Y.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso φ L M).hom.app (φ ⁻¹ᵁ U)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ
        (AlgebraicGeometry.Scheme.Modules.tensorSections s t)) =
    AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ s)
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection φ t) := by sorry
