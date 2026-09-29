-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/d5b95c8e-85fb-56d3-8b33-ba565c6b22e1
-- title:
--   Every fake elliptic curve is an ℓ-level isogeny target
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $B = \mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $B \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. an order not properly contained in any order; let $N$ be a nonzero natural number, $\ell$ a prime distinct from $q$ and $q'$, and $k$ an algebraically closed field in which $\ell$ and $N$ are nonzero. Let $E_0$ be a fake elliptic curve of level $N$ over $k$: a scheme $A$ with a smooth proper morphism to $\operatorname{Spec} k$ with connected fibres of Krull dimension $2$, a commutative relative group law on its functor of points, an action of $\Lambda$ by base-preserving endomorphisms compatible with addition and multiplication in $\Lambda$ and with the group law, normalised by the trace condition (if $m + \bar m = n$ then the induced endomorphism of the tangent space has trace $n$), together with the level-$N$ data $C$, $\mathrm{lev}$ of the structure. Then there exist a fake elliptic curve $E$ of level $N$ over $k$ and an extra level $K$ at $\ell$ on $E$ — a closed subscheme $K \hookrightarrow E.A$ whose points are closed under the group law and inversion, contain the identity, are killed by $\ell$, are $\Lambda$-stable, meet the level-$N$ subscheme only in the identity, with $K \to \operatorname{Spec} k$ finite, flat, locally of finite presentation of rank $\ell^2$, and with geometric points forming a group isomorphic to $(\mathbb{Z}/\ell)^2$ — such that `IsLevelIsogeny ℓ ⟨E, K⟩ E₀` holds: there are morphisms $\varphi : E.A \to E_0.A$ and $\psi : E_0.A \to E.A$ over $\operatorname{Spec} k$, each additive for the group laws on $T$-points and commuting with the $\Lambda$-actions, such that whenever $\ell \in \Lambda$ one has $\psi \circ \varphi = [\ell]$ on $E$ and $\varphi \circ \psi = [\ell]$ on $E_0$, a $T$-point of $E$ is annihilated by $\varphi$ if and only if it factors through $K$, and $\varphi$ carries points factoring through the level-$N$ subscheme of $E$ into that of $E_0$.
--
--   This is the surjectivity, on geometric points over an algebraically closed field, of the second degeneracy map $(E,K) \mapsto E/K$ from the moduli of fake elliptic curves with level $N$ and extra level $\ell$ to the moduli of fake elliptic curves of level $N$; it is the companion of the enumeration of extra levels, which gives surjectivity of the first degeneracy map. It is used in the study of the degeneracy maps between Shimura curves, in particular by [`CerednikDrinfeld.QM.IsCoarseModuliT.surjective_degeneracy_of_ne`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.surjective_degeneracy_of_ne) and the comparison of generic points under degeneracy.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_withExtraLevel_isLevelIsogeny.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (E₀ : FakeEllipticCurve Λ N k) :
    ∃ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, FakeEllipticCurve.IsLevelIsogeny ℓ u E₀ := by sorry
