-- Prove2me | Theorems.Thm_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft
-- name    : AlgebraicGeometry.isPullback_specMap_awayToAwayRight_awayToAwayLeft
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/90902912-7ceb-5cbd-b285-0448e0cccd08
-- title:
--   Spec R[1/fg] as fibre product of Spec R[1/f], Spec R[1/g]
-- statement:
--   Let $R$ be a commutative ring and let $f, g \in R$. Consider the four localisation maps: the $R$-algebra structure maps $R \to R_f$ and $R \to R_g$ onto the localisations away from $f$ and from $g$ (`Localization.Away f`, `Localization.Away g`), and the two maps into the localisation away from the product, namely `IsLocalization.Away.awayToAwayRight f g` $\colon R_f \to R_{fg}$ and `IsLocalization.Away.awayToAwayLeft g f` $\colon R_g \to R_{fg}$, each regarded as a ring homomorphism. Applying $\operatorname{Spec}$ to these four homomorphisms, the theorem asserts that the resulting square of schemes
--   $$\begin{array}{ccc}\operatorname{Spec} R_{fg} & \to & \operatorname{Spec} R_f\\ \downarrow & & \downarrow\\ \operatorname{Spec} R_g & \to & \operatorname{Spec} R\end{array}$$
--   is a pullback square in the category of schemes, in the sense of `IsPullback`: it commutes and the induced cone exhibits $\operatorname{Spec} R_{fg}$ as a limit, the two maps out of $\operatorname{Spec} R_{fg}$ being $\operatorname{Spec}$ of `awayToAwayRight f g` (first projection, to $\operatorname{Spec} R_f$) and $\operatorname{Spec}$ of `awayToAwayLeft g f` (second projection, to $\operatorname{Spec} R_g$). No hypotheses on $f$, $g$ or $R$ beyond commutativity are imposed.
--
--   This is the scheme-theoretic form of the identity $D(f) \cap D(g) = D(fg)$ on an affine scheme, equivalently of the isomorphism $R_f \otimes_R R_g \cong R_{fg}$. It serves gluing and descent arguments along covers by basic affine opens, whose overlaps are phrased with the `awayToAway` maps; it is used in the treatment of invertible module data and of quaternionic multiplication and polarisation data on abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isPullback_specMap_awayToAwayRight_awayToAwayLeft
    {R : Type u} [CommRing R] (f g : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g :
        Localization.Away f →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft g f :
        Localization.Away g →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) := by sorry
