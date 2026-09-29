-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/4ba305db-302d-5641-b02d-ab95d3902593
-- title:
--   Fake elliptic curves as ℓ-level isogeny images when ℓ ∣ N
-- statement:
--   Let $q \neq q'$ be primes and $a, b \in \mathbb{Q}$ be such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $a > 0$ or $b > 0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule that is an order and is maximal among orders under inclusion, let $N \neq 0$ be a natural number, let $\ell$ be a prime different from $q$ and $q'$ with $\ell \mid N$, and let $k$ be an algebraically closed field in which both $\ell$ and $N$ are nonzero. Let $E_0$ be a fake elliptic curve for $(\Lambda, N)$ over $k$, i.e. a scheme $A$ over $\operatorname{Spec} k$ carrying a commutative relative group law, smooth, proper with connected fibres, with all fibres of Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base that is additive and multiplicative and satisfies the trace condition on tangent spaces, together with its level-$N$ datum $\mathrm{lev}$. Then there exist a fake elliptic curve $E$ for $(\Lambda, N)$ over $k$ and an extra level structure $K$ at $\ell$ on $E$ — a closed immersion $K \to E.A$ whose composite to $\operatorname{Spec} k$ is finite, flat and locally of finite presentation of rank $\ell^2$, whose factoring points form a subgroup of the relative group law containing the identity, killed by $\ell$, stable under the $\Lambda$-action, meeting the level-$N$ datum of $E$ only in the identity, and isomorphic as a group to $(\mathbb{Z}/\ell)^2$ on geometric points — such that $(E, K)$ is $\ell$-level isogenous onto $E_0$: there are morphisms $\varphi : E.A \to E_0.A$ and $\psi : E_0.A \to E.A$ over $\operatorname{Spec} k$, each compatible with the relative group laws on $T$-points and with the $\Lambda$-actions, such that (whenever $\ell \in \Lambda$) $\varphi$ followed by $\psi$ is the action of $\ell$ on $E$ and $\psi$ followed by $\varphi$ is the action of $\ell$ on $E_0$, such that a point of $E$ is sent to the identity by $\varphi$ exactly when it factors through $K$, and such that $\varphi$ carries points factoring through the level-$N$ datum of $E$ to points factoring through that of $E_0$.
--
--   This is the case $\ell \mid N$ of the statement that every fake elliptic curve with level-$N$ structure over an algebraically closed field is the target of an $\ell$-level isogeny from a pair consisting of a fake elliptic curve with an extra level structure at $\ell$; this surjectivity is what makes the degeneracy map on the relevant moduli problem surjective on points. It is used, together with the complementary case $\ell \nmid N$, by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny_of_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (hℓN : ℓ ∣ N)
    (E₀ : FakeEllipticCurve Λ N k) :
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, FakeEllipticCurve.IsLevelIsogeny ℓ u E₀ := by sorry
