-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_fstHom_forall_exists_unique_smul_of_charP_of_isAlgClosed_of_three_le
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_fstHom_forall_exists_unique_smul_of_charP_of_isAlgClosed_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e49fac46-c154-54e3-9951-589150cd45f5
-- title:
--   First-order deformations of a fake elliptic curve form a line
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb Q$ and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order maximal among orders for inclusion, let $N\geq 1$ and $m\geq 3$ be integers, let $k$ be an algebraically closed field of characteristic a prime $\ell$, and assume that $N$, $m$ and $qq'$ are units in $k$. Let $u=(E,P)$ be an object of `FakeEllipticCurve.WithFullLevel Λ N m k`, i.e. a fake elliptic curve over $k$ (a scheme $A\to\operatorname{Spec} k$ with commutative relative group law, abelian-scheme property bundle, all fibres of dimension $2$, an action of $\Lambda$ by endomorphisms over the base which is additive, multiplicative and satisfies the trace condition, together with level-$N$ data) equipped with a full level-$m$ structure: a section $P$ killed by $m$ whose $\Lambda$-orbit exhausts the geometric $m$-torsion and whose annihilator in $\Lambda$ is $m\Lambda$. Write $k[\varepsilon]$ for the dual numbers, $\pi:k[\varepsilon]\to k$ for $\varepsilon\mapsto 0$, and $\sigma_c$ for the map induced by $c\cdot\mathrm{id}$ on the square-zero part, $\varepsilon\mapsto c\varepsilon$. The assertion is that there exists $v$ over $k[\varepsilon]$ such that $u$ is the base change of $v$ along $\pi$ in the sense of `WithFullLevel.IsPullback`, namely there is $g:A_u\to A_v$ making a pullback square with $\operatorname{Spec}\pi$, compatible with the group laws, commuting with the $\Lambda$-actions, carrying level-$N$ factorisations to level-$N$ factorisations, and with $P_u$ followed by $g$ equal to $\operatorname{Spec}\pi$ followed by $P_v$; and such that for every $t$ over $k[\varepsilon]$ all of whose base changes along $\pi$ are isomorphic to $u$ (isomorphism of the underlying schemes over the base respecting group law, $\Lambda$-action, level-$N$ structure and the section $P$), first there is $c\in k$ with every base change of $v$ along $\sigma_c$ isomorphic to $t$, and second such $c$ is unique: if $w$, $w'$ are base changes of $v$ along $\sigma_c$, $\sigma_{c'}$ respectively and both are isomorphic to $t$, then $c=c'$.
--
--   This is the Serre–Tate style statement that the first-order deformations of a fake elliptic curve with full level structure over an algebraically closed field of characteristic away from $Nmqq'$ form a one-dimensional $k$-space, spanned by the class of a single deformation $v$, the $k$-action being induced by the endomorphisms $\varepsilon\mapsto c\varepsilon$ of the dual numbers. It is the infinitesimal input to [`CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_finiteType_int`](thm.html#CerednikDrinfeld.QM.IsFineModuli.smoothOfRelativeDimension_one_of_finiteType_int), the smoothness of relative dimension one of the fine moduli scheme of the associated Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_fstHom_forall_exists_unique_smul_of_charP_of_isAlgClosed_of_three_le.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_fstHom_forall_exists_unique_smul_of_charP_of_isAlgClosed_of_three_le
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (k : Type) [Field k] [IsAlgClosed k]

    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hN : IsUnit ((N : ℕ) : k)) (hm' : IsUnit ((m : ℕ) : k)) (hqq'u : IsUnit ((q * q' : ℕ) : k))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k) :
    ∃ v : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k),
      FakeEllipticCurve.WithFullLevel.IsPullback (TrivSqZeroExt.fstHom k k k).toRingHom v u ∧
      ∀ t : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k),
        (∀ u' : FakeEllipticCurve.WithFullLevel Λ N m k,
          FakeEllipticCurve.WithFullLevel.IsPullback (TrivSqZeroExt.fstHom k k k).toRingHom t u' →
            FakeEllipticCurve.WithFullLevel.Iso u' u) →
        (∃ c : k, ∀ w : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k),
          FakeEllipticCurve.WithFullLevel.IsPullback
            (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w →
          FakeEllipticCurve.WithFullLevel.Iso w t) ∧
        (∀ (c c' : k) (w w' : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k)),
          FakeEllipticCurve.WithFullLevel.IsPullback
            (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w →
          FakeEllipticCurve.WithFullLevel.IsPullback
            (TrivSqZeroExt.map (R' := k) (c' • (LinearMap.id : k →ₗ[k] k))).toRingHom v w' →
          FakeEllipticCurve.WithFullLevel.Iso w t → FakeEllipticCurve.WithFullLevel.Iso w' t → c = c') := by sorry
