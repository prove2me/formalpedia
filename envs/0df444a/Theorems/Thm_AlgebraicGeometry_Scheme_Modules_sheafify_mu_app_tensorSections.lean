-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections
-- name    : AlgebraicGeometry.Scheme.Modules.sheafify_mu_app_tensorSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/a56433b7-ab8c-55ac-8d6d-e0e1c5b908b7
-- title:
--   Sheafification tensorator on sections: μ(x^#⊗ y^#)=(x⊗ y)^#
-- statement:
--   Let $X$ be a scheme and let $P$, $Q$ be presheaves of $\mathcal O_X$-modules, $U$ an open subset of $X$, and $x \in P(U)$, $y \in Q(U)$ sections. Write $(-)^{\#}$ for the functor [`AlgebraicGeometry.Scheme.Modules.sheafify X`](def/SheafOfModules_Monoidal.html#L120), the sheafification of presheaves of modules over $\mathcal O_X$ regarded as a sheaf of rings, left adjoint to the forgetful functor [`SheafOfModules.toPMod`](def/SheafOfModules_Monoidal.html#L31), and let $\mu_{P,Q} : P^{\#} \otimes Q^{\#} \to (P \otimes Q)^{\#}$ be the lax monoidal structure morphism of that functor. For sheaves of modules $L$, $M$ and sections $s \in \Gamma(L,U)$, $t \in \Gamma(M,U)$, `tensorSections` denotes the section of $L \otimes M$ over $U$ obtained by applying to $s \otimes_{\Gamma(X,U)} t$ the morphism on $U$-sections given by the unit of the sheafification adjunction at $L.\mathrm{val} \otimes M.\mathrm{val}$ followed by the comparison isomorphism `tensorIsoSheafify`. The assertion is that $\mu_{P,Q}$, evaluated on $U$ at the `tensorSections` of the images of $x$ and $y$ under the adjunction unit (so at $x^{\#} \otimes y^{\#}$ with $L = P^{\#}$, $M = Q^{\#}$), equals the image of $x \otimes_{\Gamma(X,U)} y$ under the adjunction unit at $P \otimes Q$, i.e. $(x \otimes y)^{\#}$.
--
--   This is the compatibility of the tensorator of sheafification with elementary tensors of sections: sheafification of presheaves of $\mathcal O_X$-modules is monoidal, and the comparison map sends $x^{\#}\otimes y^{\#}$ to $(x\otimes y)^{\#}$. It is the computational input used in the treatment of tensor products of quasi-coherent modules on schemes, in particular for the behaviour of local sections under pullback of tensor products and for the criterion recognising isomorphisms after pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.lean

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

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.sheafify_mu_app_tensorSections
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
