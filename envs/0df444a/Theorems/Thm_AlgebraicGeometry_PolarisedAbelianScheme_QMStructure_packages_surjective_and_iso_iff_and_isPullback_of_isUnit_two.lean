-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/4afb40f4-79d2-598a-9b74-a1b4e97cf0c6
-- title:
--   Full-level fake elliptic curves package as QM polarised schemes
-- statement:
--   Fix distinct primes $q' \neq q$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ divides $q$ or $q'$. Fix a $\mathbb{Z}$-submodule $\Lambda$ which is an order (containing $1$, closed under multiplication, spanning over $\mathbb{Q}$, finitely generated) maximal among the orders containing it; an element $\mu \in \Lambda$ with $\mu^2 = -qq'$; a map $\mathrm{star} : \Lambda \to \Lambda$ with $\mu \cdot \mathrm{star}(x) = \bar{x} \mu$ for all $x$; and $\beta : \mathrm{Fin}\,4 \to \Lambda$ such that every element of $\Lambda$ is a unique $\mathbb{Z}$-combination of the $\beta_j$. Let $m \ge 3$ and let $S$ be a commutative ring in which $2$ and $m$ are units. The conclusion is the conjunction of four assertions about the relation `Packages` between objects $u$ of `FakeEllipticCurve.WithFullLevel Λ 1 m S` (a fake elliptic curve over $S$ with $\Lambda$-action and level-$1$ datum, together with a full level-$m$ structure) and pairs consisting of $X$ in `PolarisedAbelianScheme 2 36 m S` (a commutative relative group scheme over $S$ with abelian-scheme property bundle, fibres of dimension $2$, a basis $P$ of $m$-torsion sections, and an invertible very ample sheaf with geometric fibrewise $h^0 = 36$) and a `QMStructure Λ star β X` (a $\Lambda$-action by endomorphisms of $X$ over $S$, antimultiplicative, additive, respecting the group law, satisfying the trace condition for reduced traces, with a section $P$ whose translates by $\beta_j$ are the marked torsion sections $X.P_j$, and with $X.\mathrm{pol}$ locally isomorphic on the base to the third tensor power of a canonical polarisation datum compatible with $\mathrm{star}$ via Rosati), where `Packages s u` means that there is an isomorphism $u.1.A \cong X.A$ over $\mathrm{Spec}\,S$ compatible with the group laws, intertwining the two $\Lambda$-actions, and carrying the full-level point of $u$ to the section $P$ of $s$: (i) every $u$ is packaged by some $(X,s)$; (ii) every $(X,s)$ packages some $u$; (iii) if $s$ packages $u$ and $s'$ packages $u'$, then $u$ and $u'$ are isomorphic as full-level fake elliptic curves if and only if $s$ and $s'$ are isomorphic as QM structures; (iv) for any ring homomorphism $\varphi : S \to S'$, if $s$ packages $u$ over $S$, $s'$ packages $u'$ over $S'$ and $s'$ is the $\varphi$-pullback of $s$, then $u'$ is the $\varphi$-pullback of $u$.
--
--   This is the dictionary between the moduli problem of fake elliptic curves with full level-$m$ structure for a maximal order in an indefinite quaternion algebra ramified exactly at $q$ and $q'$, and its reformulation by polarised abelian surfaces of degree data $(2,36,m)$ equipped with quaternionic multiplication. The four clauses are exactly the surjectivity, injectivity-up-to-isomorphism and base-change compatibility needed to transport representability, and it is used in the construction of a fine moduli scheme representing the pairs $(X,s)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (hm' : IsUnit ((m : ℕ) : S)) :
    (∀ u : FakeEllipticCurve.WithFullLevel Λ 1 m S,
        ∃ (X : PolarisedAbelianScheme 2 36 m S) (s : QMStructure Λ star β X), s.Packages u) ∧
    (∀ (X : PolarisedAbelianScheme 2 36 m S) (s : QMStructure Λ star β X),
        ∃ u : FakeEllipticCurve.WithFullLevel Λ 1 m S, s.Packages u) ∧
    (∀ (X X' : PolarisedAbelianScheme 2 36 m S) (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X')
        (u u' : FakeEllipticCurve.WithFullLevel Λ 1 m S), s.Packages u → s'.Packages u' →
        (FakeEllipticCurve.WithFullLevel.Iso u u' ↔ QMStructure.Iso s s')) ∧
    (∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (X : PolarisedAbelianScheme 2 36 m S) (X' : PolarisedAbelianScheme 2 36 m S')
        (s : QMStructure Λ star β X) (s' : QMStructure Λ star β X')
        (u : FakeEllipticCurve.WithFullLevel Λ 1 m S) (u' : FakeEllipticCurve.WithFullLevel Λ 1 m S'),
        s.Packages u → s'.Packages u' → QMStructure.IsPullback φ s s' →
        FakeEllipticCurve.WithFullLevel.IsPullback φ u u') := by sorry
