-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback_algebraMap_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback_algebraMap_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/4294b52e-856e-5b74-b140-a2d42c7aaad7
-- title:
--   Extension of QM structures across a discrete valuation ring
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its completion at $v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq')\cdot 1$, let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$, and let $\beta : \mathrm{Fin}\,4 \to \Lambda$ be such that every element of $\Lambda$ is uniquely an integral combination $\sum_j c_j \beta_j$. Let $d,m$ be natural numbers with $3 \le m$, let $\mathcal{O}$ be a discrete valuation domain in which $m$ is invertible, with fraction field $K$, and let $X_{\mathcal{O}}$, $X_K$ be polarised abelian schemes of relative dimension $2$, polarisation degree $d$ and level $m$ over $\mathcal{O}$ and $K$ respectively, such that $X_K$ is the base change of $X_{\mathcal{O}}$ along $\mathcal{O} \to K$ in the sense of `PolarisedAbelianScheme.IsPullback`: some morphism $g$ of total spaces makes a pullback square over $\operatorname{Spec}$ of $\mathcal{O} \to K$, is compatible with the relative group laws on points over arbitrary test schemes, carries each marked $m$-torsion section of $X_K$ to the base change of the corresponding section of $X_{\mathcal{O}}$, and identifies the pullback of the polarisation module of $X_{\mathcal{O}}$ with that of $X_K$. Then every QM structure $s_K$ on $X_K$ — an action of $\Lambda$ by endomorphisms of the total space over the base, multiplicative, additive and compatible with the group law, satisfying the tangential trace condition ($\operatorname{tr}$ of the induced map on a geometric tangent space equals $n$ whenever $x + \bar{x} = n$), equipped with a section $P$ with $\mathrm{act}(\beta_j)(P)$ the $j$-th marked section, and such that the polarisation module is, locally on the base, the third tensor power of some canonical polarisation datum for $\mathrm{star}$ — extends: there is a QM structure $s_{\mathcal{O}}$ on $X_{\mathcal{O}}$ with $s_K$ its base change along $\mathcal{O} \to K$, meaning the pullback data above additionally intertwines the two $\Lambda$-actions and matches the marked sections $P$.
--
--   This is the existence half of the valuative criterion, over discrete valuation rings, for the moduli problem of quaternionic multiplication structures on polarised abelian surfaces with full level $m$ structure in the Čerednik–Drinfeld setting: a QM structure over the fraction field spreads out over the valuation ring once the polarised abelian surface itself does. It is used in the proof that the functor of QM structures, once represented by a scheme of finite type, is universally closed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback_algebraMap_of_isDiscreteValuationRing.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_isPullback_algebraMap_of_isDiscreteValuationRing
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (hm' : IsUnit ((m : ℕ) : 𝒪))
    (X𝒪 : PolarisedAbelianScheme 2 d m 𝒪) (XK : PolarisedAbelianScheme 2 d m K)
    (hbc : PolarisedAbelianScheme.IsPullback (algebraMap 𝒪 K) X𝒪 XK)
    (sK : QMStructure Λ star β XK) :
    ∃ s𝒪 : QMStructure Λ star β X𝒪, QMStructure.IsPullback (algebraMap 𝒪 K) s𝒪 sK := by sorry
