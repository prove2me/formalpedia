-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/9eb2caf1-2e9a-5b19-9659-669d545e9a35
-- title:
--   Independence of the geometric point over 𝔭
-- statement:
--   Fix primes $q,q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a maximal order, that is an order (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning the algebra, finitely generated) maximal among the orders containing it, let $N,m\in\mathbb{N}$, let $\ell$ be a prime dividing $m$, and let $L_0\subseteq\Lambda$ be a $\mathbb{Z}$-submodule with $\ell\Lambda\subseteq L_0$, stable under left multiplication by $\Lambda$, and of relative index $\ell^2$ as an additive subgroup of $\Lambda$. Let $S$ be a commutative ring in which $m$ is a unit, $E$ a fake elliptic curve over $S$ of type $(\Lambda,N)$ with structural morphism `E.f`, relative group law `E.L`, $\Lambda$-action `E.act`, and auxiliary morphism `E.lev` into the total space of `E.f`, and let $P$ be a full level-$m$ structure on $E$. Let $\mathfrak p$ be a prime of $S$, and let $sk_0:S\to k_0$, $sk:S\to k$ be ring homomorphisms into algebraically closed fields with $\ker(sk_0)=\ker(sk)=\mathfrak p$. For an algebraically closed $k'$ and $s:S\to k'$ with kernel $\mathfrak p$, write $Q_x(s)$ for the point of `E.f` over $\operatorname{Spec} k'\to\operatorname{Spec} S$ obtained by restricting $P.P$ along that map, forming its $(m/\ell)$-fold multiple under `E.L`, and pushing it forward by the action of $x$. Assuming that for every $x\in\Lambda$ lying in $L_0$ such that $Q_x(sk_0)$ factors through `E.lev` (some morphism $\operatorname{Spec} k_0\to$ the source of `E.lev` composed with `E.lev` gives it) one has $Q_x(sk_0)$ equal to the identity section, the conclusion is the same assertion with $sk_0,k_0$ replaced by $sk,k$.
--
--   This is the statement that the transversality of the $L_0$-line through $(m/\ell)P$ to the subscheme cut out by `E.lev` depends only on the prime $\mathfrak p$ of $S$ and not on the choice of geometric point above it. It is used in the passage to the domain case, [`CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_isDomain), within the construction of auxiliary level structures on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_factorsThrough_lev_imp_eq_one_smul_fullLevel_of_ker_eq_ker
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    {S : Type} [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (P : E.FullLevel m)
    (p : PrimeSpectrum S)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (sk₀ : S →+* k₀) (hsk₀ : RingHom.ker sk₀ = p.asIdeal)
    (h₀ : ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k₀ sk₀) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k₀ sk₀)) = E.L.one (geomPoint k₀ sk₀))
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hsk : RingHom.ker sk = p.asIdeal) :
    ∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk) := by sorry
