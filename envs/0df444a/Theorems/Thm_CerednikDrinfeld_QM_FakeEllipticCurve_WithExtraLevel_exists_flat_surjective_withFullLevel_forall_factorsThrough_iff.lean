-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flat_surjective_withFullLevel_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/291c75b6-fd5c-5dc8-b07c-fb8f4748a743
-- title:
--   Flat-local full level m along a fixed line L₀
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathbb{Z}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ lies over $q$ or over $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N,m,\ell$ be naturals with $\ell$ prime and $\ell\mid m$, and let $L_0\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule with $L_0\le\Lambda$, with $\ell x\in L_0$ for all $x\in\Lambda$, with $yx\in L_0$ for all $y\in\Lambda$, $x\in L_0$, and with relative index $[\Lambda:L_0]=\ell^2$ on underlying additive groups. Let $S$ be a commutative ring in which $m$ is a unit and let $u=(E,K)$ consist of a fake elliptic curve $E$ of level $N$ over $S$ for $\Lambda$ together with an extra level structure $K$ at $\ell$ (a closed immersion `levK` into $E.A$, stable under the group law, the inverse and the $\Lambda$-action, killed by $\ell$, disjoint from the level-$N$ structure, finite flat of finite presentation of rank $\ell^2$ over $S$, with geometric fibres $\mathbb{Z}/\ell\times\mathbb{Z}/\ell$ away from $\ell$). Then there are a commutative ring $S'$ and a ring homomorphism $\varphi:S\to S'$ such that $\operatorname{Spec}\varphi$ is flat and surjective, a fake elliptic curve $E'$ of level $N$ over $S'$ with a full level-$m$ structure $P'$, and an extra level structure $K'$ on $E'$ at $\ell$, such that $(E,K)$ pulls back to $(E',K')$ along $\varphi$ — there is $g:E'.A\to E.A$ making $E'.A$ the fibre product of $E.A$ and $\operatorname{Spec}S'$ over $\operatorname{Spec}S$, compatible with the relative group laws and with the $\Lambda$-actions, and carrying points factoring through $E'.\mathrm{lev}$, respectively through `K'.levK`, to points factoring through $E.\mathrm{lev}$, respectively through `K.levK` — and such that for every algebraically closed field $k$, every ring homomorphism $s:S'\to k$ and every point $Q$ of $E'$ over the geometric point $\operatorname{Spec}k\to\operatorname{Spec}S'$ determined by $s$, the point $Q$ factors through `K'.levK` if and only if $Q=x\cdot\bigl((m/\ell)\,P'_{k,s}\bigr)$ for some $x\in\Lambda$ with $x\in L_0$, where $P'_{k,s}$ is the specialisation of $P'$ at that geometric point, $(m/\ell)$ denotes iterated addition for the group law and $x\cdot$ denotes the action of $x$ on points.
--
--   This is the variant, for pairs consisting of a fake elliptic curve and an extra level structure at $\ell$, of the statement that a full level-$m$ structure can be found after a flat surjective base change; the extra level structure is moreover identified, at every geometric point of the base, as the line $L_0$ acting on the $\ell$-division point $(m/\ell)P'$ of the full level structure. It feeds the construction of a coarse moduli scheme for the quotient level problem on Shimura curves attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flat_surjective_withFullLevel_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_forall_factorsThrough_iff
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (S : Type) [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u ⟨w'.1, K'⟩ ∧
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (Q : SchemeHomOver (geomPoint k sk) w'.1.f),
        FactorsThrough K'.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w'.1.act x) (w'.1.act_over x)
              (nsmulPt w'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w'.2.P k sk)) = Q := by sorry
