-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.sheafify_mu_app_tensorSections_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/1ee3d77c-6f43-5753-ad98-9984bf76f675
-- title:
--   Sheafification tensorator on sections: μ(x^#⊗ y^#)=(x⊗ y)^#
-- statement:
--   Let $X$ be a scheme and let $P,Q$ be presheaves of $\mathcal O_X$-modules. Write `sheafify X` for the sheafification functor from presheaves of $\mathcal O_X$-modules to sheaves of modules over the associated sheaf of rings, i.e. [`SheafOfModules.sheafifyFunctor`](def/SheafOfModules_Monoidal.html#L28) for $X$'s structure sheaf, and let the unit of the adjunction [`SheafOfModules.sheafifyAdj`](def/SheafOfModules_Monoidal.html#L35) between this functor and the forgetful-and-restriction functor [`SheafOfModules.toPMod`](def/SheafOfModules_Monoidal.html#L31) provide the sheafification maps $P \to$ `sheafify X`$(P)$ on sections. Since `sheafify X` is monoidal, it carries a tensorator $\mu_{P,Q}$ from `sheafify X`$(P) \otimes$ `sheafify X`$(Q)$ to `sheafify X`$(P \otimes Q)$. Fix an open $U \subseteq X$ and sections $x \in P(U)$, $y \in Q(U)$. Denote by $x^{\#}, y^{\#}$ their images under the unit at $U$. The assertion is an equality of sections over $U$ of `sheafify X`$(P \otimes Q)$: the component of $\mu_{P,Q}$ at $U$, applied to `tensorSections` of $x^{\#}$ and $y^{\#}$ — that is, to the image of $x^{\#} \otimes_{\Gamma(X,U)} y^{\#}$ under the unit at the presheaf tensor product followed by the comparison isomorphism `tensorIsoSheafify` — equals the image of $x \otimes_{\Gamma(X,U)} y \in (P \otimes Q)(U)$ under the unit at $P \otimes Q$.
--
--   This is the compatibility of the monoidal structure on sheafification of modules with tensor products of actual sections, in the form $\mu(x^{\#} \otimes y^{\#}) = (x \otimes y)^{\#}$; it is the basic computational handle on the tensorator. It is used in the corresponding section-level computation for the associator of the monoidal category of sheaves of modules on a scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections_monoidalV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.sheafify_mu_app_tensorSections_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (Opposite.op U)) (y : Q.obj (Opposite.op U)) :
    (Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.sheafify X) P Q).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (L := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj P)
        (M := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj Q)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app P).app (Opposite.op U) x)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app Q).app (Opposite.op U) y)) =
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (P ⊗ Q)).app (Opposite.op U)
      (x ⊗ₜ[Γ(X, U)] y) := by sorry
