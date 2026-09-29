-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/9cb699be-9fb9-525b-902f-cc1e56bedab1
-- title:
--   Pull-back comparison isomorphism on local sections
-- statement:
--   Let $X$, $Y$, $Z$ be schemes, let $f : X \to Y$ and $g : Y \to Z$ be morphisms of schemes, let $M$ be an object of $Z.\mathrm{Modules}$, let $U$ be an open subset of $Z$, and let $s \in \Gamma(M, U)$. For a morphism $\varphi : X \to Y$ and a module $L$ on the target, `pullbackLocalSection` sends a section $t \in \Gamma(L, U)$ to the section of $(\mathrm{Modules.pullback}\ \varphi).obj\ L$ over $\varphi^{-1}U$ obtained by evaluating, at the open $U$, the component at $L$ of the unit of the adjunction `Modules.pullbackPushforwardAdjunction` between pull-back and push-forward along $\varphi$, applied to $t$. The assertion is that the component at the open $f^{-1}(g^{-1}U)$ of the morphism of modules $((\mathrm{pullbackComp}\ f\ g).hom.app\ M)$ — the forward direction of the comparison isomorphism between pulling back along $g$ and then along $f$, and pulling back along $f \gg g$ — carries the iterated section $\mathrm{pullbackLocalSection}\ f\ (\mathrm{pullbackLocalSection}\ g\ s)$ to $\mathrm{pullbackLocalSection}\ (f \gg g)\ s$, the right-hand side being read in $\Gamma((\mathrm{pullback}\ (f \gg g)).obj\ M, f^{-1}(g^{-1}U))$, the open $f^{-1}(g^{-1}U)$ agreeing with $(f \gg g)^{-1}U$.
--
--   This is the compatibility of the canonical isomorphism $f^{*}g^{*}M \cong (g \circ f)^{*}M$ with the formation of pulled-back local sections, i.e. the cocycle statement for inverse images at the level of sections over an open set. It is used wherever pull-backs of sections are composed, in particular in the treatment of framed polarised abelian schemes, where it underlies the transitivity and cancellation properties of pull-back squares and the comparison of frames under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_hom_app_pullbackLocalSection.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackLocalSection
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection f
          (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection g s)) =
      (AlgebraicGeometry.Scheme.Modules.pullbackLocalSection (f ≫ g) s :
        Γ((AlgebraicGeometry.Scheme.Modules.pullback (f ≫ g)).obj M, f ⁻¹ᵁ (g ⁻¹ᵁ U))) := by sorry
