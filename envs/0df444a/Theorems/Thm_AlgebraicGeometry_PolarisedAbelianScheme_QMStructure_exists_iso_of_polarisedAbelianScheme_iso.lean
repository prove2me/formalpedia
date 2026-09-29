-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_iso_of_polarisedAbelianScheme_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/998cf5b0-efd0-53e6-9592-a3e460e345d7
-- title:
--   QM structures transport along isomorphisms of polarised abelian surfaces
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a map $\mathrm{star}:\Lambda\to\Lambda$, a family $\beta:\mathrm{Fin}(2\cdot 2)\to\Lambda$, natural numbers $d,m$, a commutative ring $S$, and two objects $X,Y$ of `PolarisedAbelianScheme 2 d m S`, each consisting of a scheme with a structure morphism to $\operatorname{Spec} S$, a commutative relative group law, the abelian-scheme property bundle, fibres of topological Krull dimension $2$, four marked sections of $m$-torsion that are independent and spanning at geometric points, and an invertible module which is very ample via a projective presentation and has geometric fibre $H^0$-rank $d$. Assume `PolarisedAbelianScheme.Iso X Y`, i.e. there is an isomorphism $e:X.A\cong Y.A$ with $e\circ$-composite to $Y.f$ equal to $X.f$, compatible with the group laws on $T$-points, carrying each marked section $X.P_i$ to $Y.P_i$, and such that the pullback of $Y.\mathrm{pol}$ along $e$ is isomorphic to $X.\mathrm{pol}$ over the preimage of a neighbourhood of every point of the base. Then for every QM structure $t$ on $X$ — a $\Lambda$-action by endomorphisms over $S$ that is additive, anti-multiplicative, unital, a homomorphism on points, satisfies the tangent-space trace condition, together with a section $P$ whose translates by $\beta_j$ are the $X.P_j$ and a canonical polarisation datum whose triple tensor product is locally isomorphic on the base to $X.\mathrm{pol}$ — there exists a QM structure $t'$ on $Y$ with `QMStructure.Iso t t'`.
--
--   This is the transport of quaternionic multiplication data along an isomorphism of linearly polarised abelian surfaces with level structure, the invariance statement needed for QM structures to define a functor on isomorphism classes. It is used in the construction of the fine moduli problem for fake elliptic curves and in the verification of the gluing and pullback properties of its affine charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_iso_of_polarisedAbelianScheme_iso.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_iso_of_polarisedAbelianScheme_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
    {d m : ℕ} {S : Type} [CommRing S] {X Y : PolarisedAbelianScheme 2 d m S}
    (h : PolarisedAbelianScheme.Iso X Y) (t : QMStructure Λ star β X) :
    ∃ t' : QMStructure Λ star β Y, QMStructure.Iso t t' := by sorry
