-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fin_isLevelIsogeny_iso_of_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/a061fd52-16c8-50de-9c67-01b1ea4c9c8f
-- title:
--   Exactly ℓ level-ℓ preimages of a generic fake elliptic curve
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb Z$-submodule which is an order maximal among orders for inclusion, let $N \ne 0$, and let $\ell$ be a prime with $\ell \ne q$, $\ell \ne q'$ and $\ell \mid N$. The assertion is that there are an $m$ and a finite list $S_0,\dots,S_{m-1}$ of fake elliptic curves of level $N$ over $\overline{\mathbb Q}$ — each a scheme over $\operatorname{Spec}\overline{\mathbb Q}$ carrying a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ by group-law endomorphisms over the base satisfying the trace condition, and a level structure $\mathrm{lev}$ — such that for every fake elliptic curve $D$ of level $N$ over $\overline{\mathbb Q}$ admitting no isomorphism (scheme isomorphism over the base respecting the group laws, commuting with the $\Lambda$-action, and matching factorisation of points through the two level structures) with any $S_j$, there are $\ell$ objects $U_0,\dots,U_{\ell-1}$, each a fake elliptic curve of level $N$ together with an extra level structure $\mathrm{levK}$ at $\ell$, with: each $U_i$ carries a level-$\ell$ isogeny to $D$, namely maps $\varphi$ from the underlying scheme of $U_i$ to that of $D$ and $\psi$ back, both over the base, additive for the group laws and $\Lambda$-equivariant, composing in either order to the action of the image of $\ell$ in $\Lambda$ (whenever $\ell$ lies in $\Lambda$), with $\varphi$ annihilating exactly the points factoring through $\mathrm{levK}$ and carrying points factoring through $\mathrm{lev}$ to such points; the $U_i$ are pairwise non-isomorphic as objects with extra level; and every object with extra level admitting a level-$\ell$ isogeny to $D$ is isomorphic to some $U_i$.
--
--   This is the fibre count of the isogeny leg $(E,K) \mapsto E/K$ of the quaternionic moduli tower at a prime $\ell$ dividing the level: outside a finite exceptional list of targets, the fibre has exactly $\ell$ points up to isomorphism. It feeds the computation of degrees in the tower, being cited by [`CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_phi_one_eq_of_dvd_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.finrankAlong_phi_one_eq_of_dvd_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_fin_isLevelIsogeny_iso_of_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_fin_isLevelIsogeny_iso_of_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ℓ ∣ N) :
    ∃ (m : ℕ) (S : Fin m → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      ∀ D : FakeEllipticCurve Λ N (AlgebraicClosure ℚ), (∀ j : Fin m, ¬ FakeEllipticCurve.Iso D (S j)) →
        ∃ U : Fin ℓ → FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
          (∀ i : Fin ℓ, FakeEllipticCurve.IsLevelIsogeny ℓ (U i) D) ∧
          (∀ i j : Fin ℓ, FakeEllipticCurve.WithExtraLevel.Iso (U i) (U j) → i = j) ∧
          (∀ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
            FakeEllipticCurve.IsLevelIsogeny ℓ u D → ∃ i : Fin ℓ, FakeEllipticCurve.WithExtraLevel.Iso u (U i)) := by sorry
