-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_packages_of_withFullLevel_of_isUnit_two
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_packages_of_withFullLevel_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/a247b777-5e9c-5dfa-b9ab-74a456276f1a
-- title:
--   Packaging fake elliptic curves as polarised abelian surfaces
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, and let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $a > 0$ or $b > 0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -qq'$, let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x} \mu$ for all $x \in \Lambda$, and let $\beta : \mathrm{Fin}\,4 \to \Lambda$ be such that every element of $\Lambda$ is a unique $\mathbb{Z}$-linear combination of the $\beta_j$. Let $m \geq 3$ and let $S$ be a commutative ring in which $2$ and $m$ are units. Then for every pair $u = (E, \mathrm{FL})$ consisting of a `FakeEllipticCurve` for $\Lambda$ with level datum $N = 1$ over $S$ together with a full level-$m$ structure on $E$, there exist a `PolarisedAbelianScheme` $X$ over $S$ of relative dimension $2$, fibre degree $36$ and torsion level $m$ — an abelian scheme with commutative relative group law and the property bundle, all fibres of dimension $2$, four $m$-torsion sections that are independent and span the $m$-torsion of every geometric fibre, and an invertible module that is a closed immersion by its sections with $h^0 = 36$ on every geometric fibre — and a `QMStructure` $s$ on $X$ for $(\Lambda, \mathrm{star}, \beta)$ such that $s$ packages $u$: there is an isomorphism $E.A \cong X.A$ over $\mathrm{Spec}\,S$ compatible with the two group laws, intertwining the $\Lambda$-actions, and carrying the level point of $\mathrm{FL}$ to the point $s.P$.
--
--   This is the surjectivity half of the comparison between the moduli problem of fake elliptic curves with full level-$m$ structure and that of polarised abelian surfaces of degree $36$ equipped with quaternionic multiplication: every fake elliptic curve arises from such a polarised object. It is cited by [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two), the statement that the forgetful comparison is a bijection compatible with base change, which underlies the representability of the Shimura curve moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_packages_of_withFullLevel_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_packages_of_withFullLevel_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (h2 : IsUnit (2 : S)) (hm' : IsUnit ((m : ℕ) : S)) :
    ∀ u : FakeEllipticCurve.WithFullLevel Λ 1 m S,
        ∃ (X : PolarisedAbelianScheme 2 36 m S) (s : QMStructure Λ star β X), s.Packages u := by sorry
