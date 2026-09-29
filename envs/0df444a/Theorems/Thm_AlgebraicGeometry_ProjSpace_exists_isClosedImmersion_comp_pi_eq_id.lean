-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_comp_pi_eq_id
-- name    : AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_comp_pi_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/49b77ce1-7e29-5205-a41b-76629a1bb747
-- title:
--   Projective space over R has a closed-immersion section
-- statement:
--   Let $R$ be a commutative ring (in a fixed universe) and let $r$ be a natural number. Write $\mathrm{Proj}$ of the graded algebra $\bigoplus_n (\text{homogeneous forms of degree } n)$ on $R[X_0,\dots,X_r]$, i.e. `Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)`, for projective $r$-space over $R$, the grading being the one by total degree on `MvPolynomial (Fin (r+1)) R`; and let `ProjSpace.π R r` denote the morphism from this scheme to $\mathrm{Spec}\,R$. The assertion is that there exists a morphism of schemes $\sigma$ from $\mathrm{Spec}\,R$ (the spectrum of $R$ viewed as an object of `CommRingCat`) to this $\mathrm{Proj}$ such that two conditions hold: $\sigma$ is a closed immersion in the sense of Mathlib's `IsClosedImmersion`, and $\sigma$ followed by `ProjSpace.π R r` is the identity morphism of $\mathrm{Spec}\,R$. Thus $\mathbb{P}^r_R$ admits an $R$-rational point whose associated section of the structure morphism is a closed immersion. No hypothesis beyond commutativity of $R$ is imposed; in particular $r = 0$ is allowed.
--
--   This records the existence of a distinguished $R$-point of $\mathbb{P}^r_R$, namely $(1:0:\dots:0)$, together with the observation that a section of the (separated) structure morphism is a closed immersion. It is used in the construction of fake elliptic curves in the Čerednik–Drinfel'd part of the development, where [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_section_forall_coe_one_comp_eq_of_tower_of_forall_isPullback) needs a closed subscheme of a projective space isomorphic to the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_comp_pi_eq_id.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_comp_pi_eq_id
    (R : Type u) [CommRing R] (r : ℕ) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R),
      IsClosedImmersion σ ∧ σ ≫ ProjSpace.π R r = 𝟙 _ := by sorry
