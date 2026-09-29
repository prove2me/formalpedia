-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_forall_away_iso
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_forall_away_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/fe27686a-61bf-5a2a-a32a-e34992b3941a
-- title:
--   Isomorphy of QM structures is local on the base
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a map $\mathrm{star}\colon\Lambda\to\Lambda$, a family $\beta\colon\mathrm{Fin}(2\cdot 2)\to\Lambda$, and naturals $d$ and $m$ with $3\le m$. Let $S$ be a commutative ring in which the image of $m$ is a unit, let $X,X'$ be objects of `PolarisedAbelianScheme 2 d m S` (abelian schemes over $\operatorname{Spec} S$ with commutative relative group law, all fibres of dimension $2$, a basis $P$ of $2\cdot 2$ $m$-torsion sections which is free of rank $2\cdot 2$ over $\mathbb{Z}/m$ on every geometric fibre, and an invertible polarisation module, very ample via a projective presentation, whose geometric fibre $H^0$ has rank $d$), and let $t$, $t'$ be `QMStructure Λ star β` data on $X$, $X'$ respectively: an action of $\Lambda$ by endomorphisms over $S$, additive and multiplicative in $\Lambda$ and additive on points, with the trace of the induced map on tangent spaces given by the reduced trace, a distinguished section $P$ whose translates under $\beta$ recover the level-structure points, and a canonical polarisation datum whose triple tensor power is locally on the base isomorphic to the given polarisation. Let $r\colon\mathrm{Fin}\,k\to S$ have $\operatorname{span}(\operatorname{range} r)=\top$, and for each $i$ let $X_i,X'_i$ be polarised abelian schemes of the same type over $\mathrm{Localization.Away}\,(r_i)$ carrying QM structures $t_i,t'_i$ such that $t_i$ (resp. $t'_i$) is a pullback of $t$ (resp. $t'$) along $S\to S[1/r_i]$ — that is, there is a cartesian comparison morphism compatible with the group laws, carrying the level points and the distinguished section to the pullbacks of those of the base, commuting with the $\Lambda$-actions, and matching polarisation modules — and such that $t_i$ and $t'_i$ are isomorphic. Then $t$ and $t'$ are isomorphic: there exist an isomorphism $e\colon X.A\cong X'.A$ over $\operatorname{Spec} S$ compatible with the group laws on points, carrying each level point $X.P\,i$ to $X'.P\,i$, pulling $X'$'s polarisation module back to $X$'s locally on the base, commuting with the two $\Lambda$-actions, and carrying the distinguished section of $t$ to that of $t'$.
--
--   This is the descent statement that isomorphy of pairs (polarised abelian surface with full level $m$ structure, quaternionic multiplication) can be checked on a distinguished affine open cover of the base, the rigidity input being $m\ge 3$ invertible. It is used in the construction of the fine moduli description of the quaternionic (fake elliptic curve) moduli problem, in particular in the analysis of the comparison map to the coarse quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_forall_away_iso.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_forall_away_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ}
    {d m : ℕ} (hm : 3 ≤ m) {S : Type} [CommRing S] (hm' : IsUnit ((m : ℕ) : S))
    {X X' : PolarisedAbelianScheme 2 d m S} (t : QMStructure Λ star β X) (t' : QMStructure Λ star β X')
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (Xl : ∀ i, PolarisedAbelianScheme 2 d m (Localization.Away (r i)))
    (tl : ∀ i, QMStructure Λ star β (Xl i))
    (Xl' : ∀ i, PolarisedAbelianScheme 2 d m (Localization.Away (r i)))
    (tl' : ∀ i, QMStructure Λ star β (Xl' i))
    (ht : ∀ i, QMStructure.IsPullback (algebraMap S (Localization.Away (r i))) t (tl i))
    (ht' : ∀ i, QMStructure.IsPullback (algebraMap S (Localization.Away (r i))) t' (tl' i))
    (hloc : ∀ i, QMStructure.Iso (tl i) (tl' i)) :
    QMStructure.Iso t t' := by sorry
