-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/ac61e4f0-c37e-5e48-9ebd-7ef04d907174
-- title:
--   Base change of full and extra level structures on fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, natural numbers $m$ and $\ell$, a further $\mathbb{Z}$-submodule $L_0$ of $\mathbb{H}[\mathbb{Q},a,b]$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$. Let $w=(E,P)$ consist of a fake elliptic curve $E$ over $S$ for the data $(\Lambda,N)$ — a scheme $A$ with a structure morphism $f$ to $\operatorname{Spec} S$, a commutative relative group law $L$, the abelian-scheme property bundle (smooth, proper, connected fibres, a group law present), two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base compatible with $L$ and additive in $\Lambda$, subject to the trace condition, together with the level datum $\mathrm{lev}$ — and of a full level-$m$ structure $P$ on $E$: a section of $f$ with $mP$ the identity, whose $\Lambda$-orbit at every geometric point of $S$ exhausts the $m$-torsion, and whose annihilator in $\Lambda$ is $m\Lambda$. Let $K$ be an extra level structure of order $\ell$ on $E$: a closed immersion $\mathrm{lev}_K$ from a scheme $K$ into $A$ whose factoring points are closed under the group law and inversion, contain the identity, are killed by $\ell$, are stable under the $\Lambda$-action, meet the points factoring through $\mathrm{lev}$ only in the identity, with $\mathrm{lev}_K$ followed by $f$ finite, flat and locally of finite presentation of fibre rank $\ell^2$, and with the factoring points at a geometric point of residue characteristic prime to $\ell$ forming a group isomorphic to $(\mathbb{Z}/\ell)^2$. Then there exist a fake elliptic curve with full level-$m$ structure $w'=(E',P')$ over $S'$ and an extra level structure $K'$ of order $\ell$ on $E'$ such that: $w'$ is a pullback of $w$ along $\varphi$, in the sense that there is a morphism $g : A' \to A$ making the square with $f'$, $f$ and $\operatorname{Spec}\varphi$ cartesian, compatible with the group laws on points, intertwining the $\Lambda$-actions, carrying points factoring through $\mathrm{lev}'$ to points factoring through $\mathrm{lev}$ after composition with $g$, and satisfying $P' \text{ followed by } g = \operatorname{Spec}\varphi$ followed by $P$; the pair $(E',K')$ is likewise a pullback of $(E,K)$ along $\varphi$, with the corresponding cartesian square, group-law and $\Lambda$-compatibilities and transfer clauses for both $\mathrm{lev}$ and $\mathrm{lev}_K$; and the following implication holds: if for every algebraically closed field $k$, every ring map $s_k : S \to k$ and every point $Q$ of $A$ over the geometric point determined by $s_k$, $Q$ factors through $\mathrm{lev}_K$ precisely when $Q$ is the image under the action of some $x \in \Lambda$ lying in $L_0$ of $(m/\ell)$ times the geometric specialisation of $P$ (with $m/\ell$ natural-number division), then the same equivalence holds for $E'$, $K'$ and $P'$ at every algebraically closed field $k$ and ring map $S' \to k$.
--
--   This is the base-change step for the moduli data of fake elliptic curves with a full level-$m$ structure and an extra level structure at $\ell$, transporting along an arbitrary ring homomorphism both pullback relations and the description of the extra level as the $L_0$-orbit of the $(m/\ell)$-multiple of the full level point. It feeds the corresponding variant statement and the construction of points of the fine moduli functor used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_extraLevel_forall_factorsThrough_iff_of_ringHom
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ) :
    ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
      FakeEllipticCurve.WithFullLevel.IsPullback φ w w' ∧
      FakeEllipticCurve.WithExtraLevel.IsPullback φ (⟨w.1, K⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨w'.1, K'⟩ ∧
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w.1.act x) (w.1.act_over x)
              (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q) →
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (Q : SchemeHomOver (geomPoint k sk) w'.1.f),
        FactorsThrough K'.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w'.1.act x) (w'.1.act_over x)
              (nsmulPt w'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w'.2.P k sk)) = Q) := by sorry
