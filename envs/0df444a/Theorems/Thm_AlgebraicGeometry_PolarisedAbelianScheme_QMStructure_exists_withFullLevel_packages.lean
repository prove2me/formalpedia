-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_withFullLevel_packages
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/325b8f47-6c56-5a31-9757-67f967cba612
-- title:
--   Unpacking a QM structure into a fake elliptic curve
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders containing it, let $\mu\in\Lambda$ satisfy $\mu^{2}=-(qq')\cdot 1$, let $\star:\Lambda\to\Lambda$ satisfy $\mu\,x^{\star}=\bar{x}\mu$ for all $x\in\Lambda$, and let $\beta:\mathrm{Fin}(2\cdot 2)\to\Lambda$ be such that every $x\in\Lambda$ has a unique expansion $x=\sum_j c_j\beta_j$ with $c\in\mathbb{Z}^{4}$. Let $m\geq 3$ and let $S$ be a commutative ring in which $m$ is a unit. The assertion is that for every $X:\mathrm{PolarisedAbelianScheme}\ 2\ 36\ m\ S$ — a scheme $X.A$ over $\mathrm{Spec}\,S$ carrying a commutative relative group law, an abelian-scheme property bundle, all fibres of topological Krull dimension $2$, four $m$-torsion sections that on every geometric fibre over an algebraically closed field are independent and span the $m$-torsion, and an invertible module $X.\mathrm{pol}$ which is a closed immersion by sections into projective space with geometric fibre $H^{0}$-rank $36$ — and every $s:\mathrm{QMStructure}\ \Lambda\ \star\ \beta\ X$ — an action of $\Lambda$ by endomorphisms of $X.A$ over $\mathrm{Spec}\,S$ which is additive, sends products to reversed composites, sends $1$ to the identity, is compatible with the group law on points, satisfies the trace condition matching $\mathrm{tr}(\Phi)$ on tangent spaces with $x+\bar{x}\in\mathbb{Z}$, together with a section $P$ whose translates $\beta_j\cdot P$ are the four level sections of $X$, and a module $\mathrm{polE}$ satisfying `IsCanonicalPolData` with $X.\mathrm{pol}$ locally on the base isomorphic to $\mathrm{polE}^{\otimes 3}$ — there exists a pair $u$ consisting of a fake elliptic curve $E$ over $S$ for $\Lambda$ with $\Gamma_0$-level $N=1$ and a full level-$m$ structure on $E$, such that $s.\mathrm{Packages}\ u$ holds: an isomorphism $e:u.1.A\cong X.A$ with $e$ followed by $X.f$ equal to $u.1.f$, compatible with the two group laws on points over any base, intertwining the $\Lambda$-actions, and carrying the level generator $u.2.P$ to $s.P$.
--
--   This is the surjectivity ("unpacking") half of the comparison between polarised abelian surfaces with quaternionic multiplication and full level structure on the one hand, and fake elliptic curves with level structure on the other, in the Čerednik–Drinfeld description of Shimura curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$. It is cited by [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.packages_surjective_and_iso_iff_and_isPullback_of_isUnit_two), where the two moduli descriptions are identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_withFullLevel_packages.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_withFullLevel_packages
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (m : ℕ) (hm : 3 ≤ m) (S : Type) [CommRing S] (hm' : IsUnit ((m : ℕ) : S)) :
    ∀ (X : PolarisedAbelianScheme 2 36 m S) (s : QMStructure Λ star β X),
        ∃ u : FakeEllipticCurve.WithFullLevel Λ 1 m S, s.Packages u := by sorry
