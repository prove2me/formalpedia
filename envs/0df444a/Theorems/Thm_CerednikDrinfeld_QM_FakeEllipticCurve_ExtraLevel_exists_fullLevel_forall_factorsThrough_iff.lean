-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_fullLevel_forall_factorsThrough_iff
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/2f063b28-bdd9-577d-88e3-700ea291f08f
-- title:
--   Every extra level at ℓ has the form L₀·(m/ℓ)P
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it. Fix $N,m\in\mathbb{N}$, a prime $\ell$ dividing $m$, and a $\mathbb{Z}$-submodule $L_0\subseteq\Lambda$ with $\ell x\in L_0$ for all $x\in\Lambda$, stable under left multiplication by $\Lambda$, and of relative index $\ell^2$ in $\Lambda$ as additive subgroups. Let $k$ be an algebraically closed field with $m\neq 0$ in $k$, let $E$ be a fake elliptic curve over $k$ for $\Lambda$ and $N$ (an abelian scheme $E.f:E.A\to\operatorname{Spec}k$ with commutative relative group law $E.L$, two-dimensional fibres and an action of $\Lambda$), and let $K$ be an extra level at $\ell$ on $E$: a closed immersion $K.\mathrm{levK}$ into $E.A$, finite, flat and locally of finite presentation of rank $\ell^2$ over the base, whose points form a subgroup killed by $\ell$, stable under $\Lambda$, meeting $E.\mathrm{lev}$ only in the identity, and with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$ as groups. Then there is a full level-$m$ structure $P$ on $E$ — a section $P.P$ of $E.f$ killed by $m$ whose $\Lambda$-orbit exhausts the $m$-torsion at every algebraically closed geometric point, and whose annihilator in $\Lambda$ is $m\Lambda$ — such that for every algebraically closed field $k'$, every ring homomorphism $sk:k\to k'$ and every point $Q$ of $E.A$ over the geometric point $\operatorname{Spec}k'\to\operatorname{Spec}k$ determined by $sk$, the point $Q$ factors through $K.\mathrm{levK}$ (that is, $Q$ is $\mathrm{levK}$ precomposed with some morphism $\operatorname{Spec}k'\to K.K$) if and only if $Q=x\cdot\bigl((m/\ell)\,P\bigr)$ for some $x\in\Lambda$ lying in $L_0$, where $(m/\ell)P$ denotes the $(m/\ell)$-fold multiple of the base change of $P.P$ for the group law $E.L$ and $x\cdot$ denotes the action of $E.\mathrm{act}\,x$ on points. The hypothesis on $N$ is only that of being a natural number entering the datum of $E$.
--
--   This is the rigidification step in the moduli description of extra level structures on fake elliptic curves: after fixing once and for all a $\Lambda$-stable line $L_0$ of index $\ell^2$ in $\Lambda$, every extra level at $\ell$ over an algebraically closed field is realised as the $L_0$-orbit of $(m/\ell)P$ for a suitable full level-$m$ structure $P$, so that the pair $(E,K)$ is determined by level-$m$ data alone. It is used in the construction of a coarse moduli description of the quotient of the relevant Shimura curve by the extra level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_fullLevel_forall_factorsThrough_iff.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_fullLevel_forall_factorsThrough_iff
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m : ℕ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓm : ℓ ∣ m)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_left : ∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L₀ → (y : ℍ[ℚ, a, b]) * x ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (k : Type) [Field k] [IsAlgClosed k] (hm : (m : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (K : E.ExtraLevel ℓ) :
    ∃ P : E.FullLevel m,
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k' sk)) = Q := by sorry
