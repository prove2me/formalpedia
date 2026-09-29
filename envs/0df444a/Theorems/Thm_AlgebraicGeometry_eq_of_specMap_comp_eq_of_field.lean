-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field
-- name    : AlgebraicGeometry.eq_of_specMap_comp_eq_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3550dc8b-7dd3-55d5-b9b8-f689549e6bbf
-- title:
--   Field-valued points are determined after field extension
-- statement:
--   Let $X$ be a scheme (with underlying data in the lowest universe), let $\kappa$ and $\kappa'$ be fields, and let $i \colon \kappa \to \kappa'$ be a ring homomorphism. Let $P, Q \colon \operatorname{Spec}\kappa \to X$ be two morphisms of schemes, where $\operatorname{Spec}\kappa$ denotes the spectrum of $\kappa$ viewed as an object of `CommRingCat`. Suppose that pre-composing both with the morphism $\operatorname{Spec}(i) \colon \operatorname{Spec}\kappa' \to \operatorname{Spec}\kappa$ induced by $i$ gives equal morphisms, i.e. $\operatorname{Spec}(i)$ followed by $P$ equals $\operatorname{Spec}(i)$ followed by $Q$ as morphisms $\operatorname{Spec}\kappa' \to X$. Then $P = Q$. Equivalently, $\operatorname{Spec}(i)$ is an epimorphism in the category of schemes for every homomorphism of fields $i$; no flatness, finiteness or algebraicity assumption on the extension $\kappa'/\kappa$ is needed, only that source and target are fields.
--
--   This is the standard fact that a $\kappa$-valued point of a scheme is determined by the $\kappa'$-valued point it induces along any field extension, equivalently that $\operatorname{Spec}\kappa' \to \operatorname{Spec}\kappa$ is an epimorphism of schemes. It is used to descend statements about points of group schemes from a larger field (typically an algebraic closure) to the original field: it is cited in the treatment of Riemann forms, to show a certain morphism vanishes once its composite with a translation does, and in the Čerednik–Drinfel'd part of the argument, to show that a torsion point of a fake elliptic curve is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_specMap_comp_eq_of_field
    {X : Scheme.{0}} {κ κ' : Type} [Field κ] [Field κ'] (i : κ →+* κ')
    (P Q : Spec (CommRingCat.of κ) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom i) ≫ P = Spec.map (CommRingCat.ofHom i) ≫ Q) :
    P = Q := by sorry
