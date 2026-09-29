-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_withFullLevel_isPullback_of_packages_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.withFullLevel_isPullback_of_packages_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/4ffeaf4c-51a0-5b7a-87fc-aacad1a42d77
-- title:
--   Packaging is compatible with base change
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $a>0$ or $b>0$ and, for a finite place $v$ of $\mathbb Q$, the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly when $v$ lies over $q$ or $q'$; fix a maximal order $\Lambda$ (an order contained in no strictly larger order), an element $\mu \in \Lambda$ with $\mu^2 = -qq'$, a map $\star$ on $\Lambda$ with $\mu\,x^{\star} = \bar x\,\mu$ for all $x$, a family $\beta : \mathrm{Fin}\,4 \to \Lambda$ that is a $\mathbb Z$-basis of $\Lambda$ (each $x$ is uniquely $\sum_j c_j\beta_j$ with $c_j \in \mathbb Z$), an integer $m \geq 3$ and a commutative ring $S$ in which $m$ is invertible. The assertion is that for every commutative ring $S'$, ring homomorphism $\varphi : S \to S'$, polarised abelian schemes $X$ over $S$ and $X'$ over $S'$ of relative dimension $2$, fibre invariant $36$ and level $m$, quaternionic structures $s$ on $X$ and $s'$ on $X'$ relative to $(\Lambda,\star,\beta)$, and objects $u = (E, \text{full level } m)$ over $S$ and $u'$ over $S'$ consisting of a fake elliptic curve for $\Lambda$ of level $1$ together with a full $m$-level structure: if $s$ packages $u$ and $s'$ packages $u'$ — that is, there are isomorphisms $e : u.1.A \cong X.A$ and $e' : u'.1.A \cong X'.A$ over the respective bases, compatible with the group laws on points, intertwining the $\Lambda$-actions, and carrying the distinguished level points to $s.P$, $s'.P$ — and if $s'$ is the base change of $s$ along $\varphi$ in the sense of `QMStructure.IsPullback` (a morphism $g_A : X'.A \to X.A$ whose square with the structure morphisms and $\mathrm{Spec}\,\varphi$ is cartesian, additive on $T$-points, carrying the four torsion sections $X'.P_i$ to $\mathrm{Spec}\,\varphi$ followed by $X.P_i$, with $g_A^{*}X.\mathrm{pol} \cong X'.\mathrm{pol}$, intertwining the actions of $\Lambda$ and carrying $s'.P$ to $\mathrm{Spec}\,\varphi$ followed by $s.P$), then $u'$ is the base change of $u$ along $\varphi$ in the sense of `FakeEllipticCurve.WithFullLevel.IsPullback`: there is $g : u'.1.A \to u.1.A$ forming a cartesian square over $\mathrm{Spec}\,\varphi$, additive on $T$-points, commuting with the $\Lambda$-action, such that every $T$-point of $u'$ factoring through $u'.1.\mathrm{lev}$ is carried by $g$ to a point factoring through $u.1.\mathrm{lev}$, and $g$ carries the level point of $u'$ to $\mathrm{Spec}\,\varphi$ followed by that of $u$.
--
--   This is the base-change clause in the comparison between quaternionic structures on polarised abelian schemes with level $m$ and fake elliptic curves with full level $m$ structure, used in the Čerednik–Drinfeld part of the construction of Shimura curves as moduli; it is cited by the combined statement that packaging is surjective, determines the object up to isomorphism, and commutes with base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_withFullLevel_isPullback_of_packages_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.withFullLevel_isPullback_of_packages_of_isPullback
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (hm' : IsUnit ((m : ℕ) : S)) :
    ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S')
        (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X')
        (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m S'),
        s.Packages u → s'.Packages u' → QMStructure.IsPullback φ s s' →
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u' := by sorry
