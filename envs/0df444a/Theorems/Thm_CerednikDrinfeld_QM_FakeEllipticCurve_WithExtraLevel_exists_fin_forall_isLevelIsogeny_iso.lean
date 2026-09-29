-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fin_forall_isLevelIsogeny_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_forall_isLevelIsogeny_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/60cc52a0-da81-5177-99cd-e03255759a91
-- title:
--   Finitely many level-ℓ isogeny sources over a fake elliptic curve
-- statement:
--   Let $q$ and $q'$ be primes with $q' \neq q$, let $a,b \in \mathbb{Q}$, and suppose the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a > 0$ or $b > 0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the base change $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders under inclusion, let $N$ be a nonzero natural number and $\ell$ a prime, let $k$ be an algebraically closed field in which $\ell$ and $N$ are nonzero, and let $D$ be a fake elliptic curve of level $N$ over $k$ for $\Lambda$ in the sense of `FakeEllipticCurve`: a $k$-scheme with a commutative relative group law, the abelian-scheme property bundle, all fibres of Krull dimension $2$, an action of $\Lambda$ by fibrewise group-law endomorphisms satisfying the additivity, multiplicativity and reduced-trace conditions, together with the level-$N$ datum $\mathrm{lev}$. Then there are a natural number $m$ and a family $U : \mathrm{Fin}\, m \to$ `FakeEllipticCurve.WithExtraLevel` $\Lambda\, N\, \ell\, k$ of pairs (a fake elliptic curve of level $N$ together with an extra level structure at $\ell$) such that every pair $u$ admitting a level-$\ell$ isogeny onto $D$ — that is, mutually inverse-up-to-$\ell$ morphisms $\varphi$ and $\psi$ over $\operatorname{Spec} k$, both homomorphisms for the group laws on points and both $\Lambda$-equivariant, with $\psi \circ \varphi$ and $\varphi \circ \psi$ the action of $\ell$ whenever $\ell \in \Lambda$, whose $\varphi$ kills exactly the points factoring through the $\ell$-level datum of $u$ and carries points factoring through $\mathrm{lev}$ into the level datum of $D$ — is isomorphic, in the sense of `WithExtraLevel.Iso` (an isomorphism of the underlying schemes over $\operatorname{Spec} k$ compatible with the group laws and the $\Lambda$-actions and matching both the level-$N$ and the level-$\ell$ data), to some $U\, i$. Repetitions in the family and $m = 0$ are allowed, so the assertion is that the isomorphism classes of such $u$ are covered by a finite list.
--
--   This is the finiteness statement underlying the degeneracy maps between Shimura-curve moduli of fake elliptic curves with and without extra level structure at $\ell$: the fibre of the forgetful map over a given fake elliptic curve $D$ meets only finitely many isomorphism classes. It is used in the proof that the degeneracy map on coarse moduli is finite ([`CerednikDrinfeld.QM.IsCoarseModuliT.isFinite_degeneracy`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.isFinite_degeneracy)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fin_forall_isLevelIsogeny_iso.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_forall_isLevelIsogeny_iso
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (D : FakeEllipticCurve Λ N k) :
    ∃ (m : ℕ) (U : Fin m → FakeEllipticCurve.WithExtraLevel Λ N ℓ k),
      ∀ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k, FakeEllipticCurve.IsLevelIsogeny ℓ u D →
        ∃ i : Fin m, FakeEllipticCurve.WithExtraLevel.Iso u (U i) := by sorry
