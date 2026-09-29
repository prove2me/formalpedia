-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flip_of_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flip_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/c007109b-ac49-5c00-af14-eee2db5573d3
-- title:
--   An ℓ-isogeny flip on fake elliptic curves with ℓ-level
-- statement:
--   Let $q \neq q'$ be primes and $a, b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a > 0$ or $b > 0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (an order, and every order containing it equals it), let $N$ be a nonzero natural number, and let $\ell$ be a prime with $\ell \neq q$, $\ell \neq q'$ and $\ell \nmid N$. Write $\mathcal{M}$ for the type `FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)` of pairs $u = (E, \kappa)$ consisting of a fake elliptic curve $E$ of level $N$ with $\Lambda$-action over $\overline{\mathbb{Q}}$ together with an `ExtraLevel ℓ` datum $\kappa$ for $E$, whose morphism `levK` into `E.A` records the level structure at $\ell$. Then there is a map $\mathrm{fl} : \mathcal{M} \to \mathcal{M}$ with three properties. First, for every $u$ the pair $(u, (\mathrm{fl}\,u).1)$ satisfies `IsLevelIsogeny ℓ`: there are morphisms $\varphi : u.1.A \to (\mathrm{fl}\,u).1.A$ and $\psi$ in the opposite direction, both over $\operatorname{Spec} \overline{\mathbb{Q}}$, compatible with the relative group laws and commuting with the $\Lambda$-actions, such that (whenever the rational scalar $\ell$ lies in $\Lambda$) $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$ are the actions of $\ell$ on source and target, such that a point of $u.1$ is sent to the identity by $\varphi$ precisely when it factors through $u.2$'s `levK`, and such that points factoring through the level-$N$ structure of $u.1$ are carried by $\varphi$ to points factoring through that of $(\mathrm{fl}\,u).1$. Secondly, $\mathrm{fl}$ preserves the relation `WithExtraLevel.Iso` (an isomorphism of the underlying schemes over the base compatible with the group laws, the $\Lambda$-actions and the two level data): if $u$ and $v$ are isomorphic so are $\mathrm{fl}\,u$ and $\mathrm{fl}\,v$. Thirdly, $\mathrm{fl}(\mathrm{fl}\,u)$ is isomorphic to $u$ for every $u$, so that $\mathrm{fl}$ is an involution up to isomorphism rather than on the nose.
--
--   This is the flip $(E,K) \mapsto (E/K, E[\ell]/K)$ on pairs of a fake elliptic curve with level-$\ell$ structure, the analogue of the Atkin–Lehner involution $w_\ell$ on the $\ell$-level of a Shimura curve; the hypothesis $\ell \nmid N$ is what makes the image level structure disjoint from the level-$N$ structure. It is used in the construction of the Čerednik–Drinfeld moduli tower, where it supplies the interchange of the two degeneracy maps at $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flip_of_not_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flip_of_not_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ¬ ℓ ∣ N) :
    ∃ fl : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ) →
        FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
      (∀ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
        FakeEllipticCurve.IsLevelIsogeny ℓ u (fl u).1) ∧
      (∀ u v : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
        FakeEllipticCurve.WithExtraLevel.Iso u v → FakeEllipticCurve.WithExtraLevel.Iso (fl u) (fl v)) ∧
      (∀ u : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ),
        FakeEllipticCurve.WithExtraLevel.Iso (fl (fl u)) u) := by sorry
