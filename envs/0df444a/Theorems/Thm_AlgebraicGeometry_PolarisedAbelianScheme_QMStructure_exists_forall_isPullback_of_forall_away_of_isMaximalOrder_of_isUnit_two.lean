-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_forall_isPullback_of_forall_away_of_isMaximalOrder_of_isUnit_two
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_forall_isPullback_of_forall_away_of_isMaximalOrder_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/8c9dccf5-f5bf-5727-9e00-c3a2adae25cf
-- title:
--   Gluing QM structures over a basic open cover, 2 invertible
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and $a,b\in\mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every finite place $v$ of $\mathbb{Q}$, the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ lies above $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, $\mu\in\Lambda$ with $\mu^2=-(qq')\cdot 1$, $\mathrm{star}:\Lambda\to\Lambda$ a map with $\mu\,\mathrm{star}(x)=\bar{x}\mu$ for all $x$, and $\beta:\mathrm{Fin}\,4\to\Lambda$. Let $m\geq 3$, let $S$ be a commutative ring in which $2$ and $m$ are units, and let $X$ be a polarised abelian scheme over $S$ of relative dimension $2$, fibre degree $d$ and full level $m$ (group law, abelian-scheme property bundle, $4$ independent spanning $m$-torsion sections, and a very ample invertible module of geometric fibre rank $d$). Let $r:\mathrm{Fin}\,k\to S$ generate the unit ideal, and for each $i$ let $X_i$ be a polarised abelian scheme over $\mathrm{Localization.Away}\,(r_i)$ which is a pullback of $X$ along $S\to S[1/r_i]$, equipped with a structure $t_i:\mathrm{QMStructure}\ \Lambda\ \mathrm{star}\ \beta\ X_i$: an action of $\Lambda$ by endomorphisms over the base which is additive and antimultiplicative, is compatible with the group law, has trace on geometric tangent spaces equal to the reduced trace, carries a section $P$ with $\mathrm{act}(\beta_j)\circ P$ the $j$-th marked level point, and admits a canonical polarisation datum $\mathcal{L}$ with $X_i.\mathrm{pol}$ locally isomorphic over the base to $\mathcal{L}^{\otimes 3}$. Assume the $t_i$ agree on overlaps: for all $i,j$ and all polarised abelian schemes $Y,Y'$ over $S[1/(r_ir_j)]$ with such structures $s,s'$, if $s$ is a pullback of $t_i$ along $S[1/r_i]\to S[1/(r_ir_j)]$ and $s'$ a pullback of $t_j$ along $S[1/r_j]\to S[1/(r_ir_j)]$, then $s$ and $s'$ are isomorphic (an isomorphism of the underlying abelian schemes respecting group law, level points, polarisation locally on the base, the $\Lambda$-actions and the distinguished sections). Then there is a structure $t:\mathrm{QMStructure}\ \Lambda\ \mathrm{star}\ \beta\ X$ whose pullback along $S\to S[1/r_i]$ is $t_i$ for every $i$.
--
--   This is the Zariski descent (gluing) step for quaternionic multiplication data on polarised abelian surfaces with full level $m\geq 3$: a family of QM structures on the base changes of $X$ to a cover by basic opens, agreeing on the pairwise overlaps, descends to a single QM structure on $X$. It feeds the construction of the fine and coarse moduli of fake elliptic curves in the Čerednik–Drinfeld setting, and is used in the analysis of the map recording a QM structure on affine charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_forall_isPullback_of_forall_away_of_isMaximalOrder_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_forall_isPullback_of_forall_away_of_isMaximalOrder_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ)
    {d m : ℕ} (hm : 3 ≤ m) {S : Type} [CommRing S] (h2 : IsUnit (2 : S)) (hm' : IsUnit ((m : ℕ) : S))
    (X : PolarisedAbelianScheme 2 d m S)
    {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (Xl : ∀ i, PolarisedAbelianScheme 2 d m (Localization.Away (r i)))
    (hXl : ∀ i, PolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r i))) X (Xl i))
    (tl : ∀ i, QMStructure Λ star β (Xl i))
    (hagree : ∀ (i j : Fin k)
      (Y : PolarisedAbelianScheme 2 d m (Localization.Away (r i * r j))) (s : QMStructure Λ star β Y)
      (Y' : PolarisedAbelianScheme 2 d m (Localization.Away (r i * r j))) (s' : QMStructure Λ star β Y'),
      QMStructure.IsPullback
        (IsLocalization.Away.awayToAwayRight (r i) (r j) : Localization.Away (r i) →+* Localization.Away (r i * r j)) (tl i) s →
      QMStructure.IsPullback
        (IsLocalization.Away.awayToAwayLeft (r j) (r i) : Localization.Away (r j) →+* Localization.Away (r i * r j)) (tl j) s' →
      QMStructure.Iso s s') :
    ∃ t : QMStructure Λ star β X, ∀ i, QMStructure.IsPullback (algebraMap S (Localization.Away (r i))) t (tl i) := by sorry
