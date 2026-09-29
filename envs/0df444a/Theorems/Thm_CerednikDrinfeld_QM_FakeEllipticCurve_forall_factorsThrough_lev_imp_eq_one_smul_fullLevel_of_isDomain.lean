-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/28c4e28d-bb91-557a-9d49-89801e0305e2
-- title:
--   Transversality spreads from one geometric point over a domain
-- statement:
--   Fix primes $q,q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $q\in v$ or $q'\in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N,m$ be naturals, $\ell$ a prime with $\ell\mid m$, and let $L_0$ be a $\mathbb{Z}$-submodule with $L_0\subseteq\Lambda$, $\ell\cdot\Lambda\subseteq L_0$, $\Lambda\cdot L_0\subseteq L_0$, and $[\Lambda:L_0]=\ell^2$ as additive groups. Let $S$ be a commutative domain in which $m$ and $N$ are units, $E$ a `FakeEllipticCurve` for $\Lambda$ of level $N$ over $S$, and $P$ a full level-$m$ structure on $E$. Suppose that for one algebraically closed field $k_0$ and one ring homomorphism $sk_0\colon S\to k_0$ the following holds: for every $x\in\Lambda$ lying in $L_0$, if the point obtained by applying the action $E.\mathrm{act}\,x$ to the $(m/\ell)$-fold multiple, under the relative group law $E.L$, of the base change of $P.P$ along $\operatorname{Spec}(sk_0)$ factors through the morphism `E.lev` (i.e. its underlying scheme morphism is $E.\mathrm{lev}$ precomposed with some morphism to the source of `E.lev`), then that point is the identity section at $\operatorname{Spec}(sk_0)$. Then the same implication holds for every algebraically closed field $k$ and every ring homomorphism $sk\colon S\to k$.
--
--   This is the spreading-out step which upgrades the transversality of the $L_0$-line through $(m/\ell)P$ to the level datum of a fake elliptic curve from a single geometric point of $\operatorname{Spec} S$ to all of them, over an integral base; it supplies the disjointness hypothesis needed to construct an extra level structure over the whole base. It is used in the construction of algebraic families with extra level on the quaternionic fine moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (hN : IsUnit ((N : ℕ) : S)) [IsDomain S]
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (sk₀ : S →+* k₀)
    (h₀ : ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀)) = E.L.one (geomPoint k₀ sk₀)) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk) := by sorry
