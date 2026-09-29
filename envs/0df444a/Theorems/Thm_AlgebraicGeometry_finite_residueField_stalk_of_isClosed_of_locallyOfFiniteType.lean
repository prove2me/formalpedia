-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d8223c4a-8b3f-563d-8bde-067125a0e3ad
-- title:
--   Finite residue field at a closed point over a finite residue field
-- statement:
--   Let $R$ be a commutative local ring whose residue field $\mathrm{ResidueField}(R) = R/\mathfrak m_R$ is finite, let $Y$ be a scheme, and let $\pi_Y : Y \to \operatorname{Spec} R$ be a morphism of schemes which is locally of finite type. Let $y$ be a point of $Y$ such that the singleton $\{y\}$ is closed in the underlying topological space of $Y$, and such that the image of $y$ under $\pi_Y$ is the closed point of $\operatorname{Spec} R$, i.e. the prime corresponding to $\mathfrak m_R$. Then the residue field of the local ring $\mathcal O_{Y,y}$, i.e. the quotient of the stalk of the structure presheaf of $Y$ at $y$ by its maximal ideal, is a finite type. Both base and source are taken in a single universe $u$, and $\operatorname{Spec} R$ is formed from $R$ viewed as an object of the category of commutative rings.
--
--   This is the scheme-theoretic form of Zariski's Nullstellensatz used for residue fields: a closed point of a scheme locally of finite type over a local ring with finite residue field, lying over the closed point of the base, has finite residue field. It is used in the study of stalks of the moduli problems occurring later, being cited by [`AlgebraicGeometry.isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy`](thm.html#AlgebraicGeometry.isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy) and by [`CerednikDrinfeld.QM.IsFineModuli.exists_isRegularLocalRing_prorepresents_stalk_of_isClosed`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isRegularLocalRing_prorepresents_stalk_of_isClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType
    {R : Type u} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType πY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyR : πY y = IsLocalRing.closedPoint R) :
    Finite (IsLocalRing.ResidueField (Y.presheaf.stalk y)) := by sorry
