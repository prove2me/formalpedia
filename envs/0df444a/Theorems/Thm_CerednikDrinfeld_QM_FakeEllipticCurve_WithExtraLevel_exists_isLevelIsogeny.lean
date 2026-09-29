-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isLevelIsogeny
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isLevelIsogeny
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/8aca924c-efb1-59f9-a0d8-488670473fd9
-- title:
--   Quotient by an extra ℓ-level exists over ̄ k
-- statement:
--   Let $q \neq q'$ be primes and $a,b \in \mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N \geq 1$, let $\ell$ be a prime distinct from $q$ and $q'$, and let $k$ be an algebraically closed field in which $\ell$ and $N$ are nonzero. Let $u = (E,K)$ consist of a fake elliptic curve $E$ of level $N$ over $k$ with $\Lambda$-action (an abelian scheme with commutative relative group law, fibres of topological Krull dimension $2$, a $\Lambda$-action by base-preserving endomorphisms satisfying the additivity, multiplicativity and trace conditions, together with the level-$N$ data) and an extra level structure $K$ at $\ell$ for $E$: a closed immersion $\mathrm{lev}_K : K \to E.A$, finite, flat and locally of finite presentation over $k$ of rank $\ell^2$, whose $T$-points form a subgroup containing the identity, killed by $\ell$, stable under $\Lambda$, meeting the level-$N$ subscheme only in the identity, and isomorphic as a group to $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ on geometric points. Then there exists a fake elliptic curve $E'$ of level $N$ over $k$ with `FakeEllipticCurve.IsLevelIsogeny ℓ u E'`: morphisms $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ over $k$, each additive on $T$-points and commuting with the $\Lambda$-actions, such that whenever $\ell \in \Lambda$ the composites $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ are the actions of $\ell$ on $E.A$ and $E'.A$ respectively, a $T$-point $P$ of $E$ satisfies $\varphi(P) = 0$ exactly when $P$ factors through $K$, and $\varphi$ sends points factoring through the level-$N$ subscheme of $E$ to points factoring through that of $E'$.
--
--   This is the existence of the quotient $E/K$ as a fake elliptic curve with $\Lambda$-action and level-$N$ structure, over an algebraically closed base: on geometric points it is the second degeneracy map $(E,K) \mapsto E/K$ from the Shimura curve with level raised at $\ell$ to the Shimura curve of level $N$. It feeds the constructions of level structures and isogenies on fake elliptic curves, in particular [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny) and the statements producing extra levels from sublattices and point equivalences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isLevelIsogeny.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isLevelIsogeny
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) :
    ∃ E' : FakeEllipticCurve Λ N k, FakeEllipticCurve.IsLevelIsogeny ℓ u E' := by sorry
