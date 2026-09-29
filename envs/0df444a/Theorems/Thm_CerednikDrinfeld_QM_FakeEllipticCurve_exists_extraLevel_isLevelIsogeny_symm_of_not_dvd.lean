-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_symm_of_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_symm_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/68b4be8e-cf9f-5437-a98a-d6d112d9b3ca
-- title:
--   Symmetry of ℓ-level isogenies of fake elliptic curves
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, $N \geq 1$, and $\ell$ a prime with $\ell \neq q$, $\ell \neq q'$ and $\ell \nmid N$; let $k$ be an algebraically closed field in which $\ell$ and $N$ are nonzero. Let $u = (E,K)$ consist of a fake elliptic curve $E$ of level $N$ over $k$ together with an extra level $K$ at $\ell$ on $E$, and let $E'$ be a fake elliptic curve of level $N$ over $k$ with `IsLevelIsogeny ℓ u E'`: there are morphisms $\varphi \colon E.A \to E'.A$ and $\psi \colon E'.A \to E.A$ over $\operatorname{Spec} k$, additive on $T$-points for the relative group laws, commuting with the $\Lambda$-actions, with $\psi \circ \varphi$ and $\varphi \circ \psi$ the actions of $\ell$ whenever $\ell \in \Lambda$, whose $T$-points killed by $\varphi$ are exactly those factoring through $K$, and with $\varphi$ carrying points factoring through the level-$N$ structure of $E$ into that of $E'$. The conclusion asserts the existence of an extra level $K'$ at $\ell$ on $E'$ — a closed subscheme of $E'.A$ closed under the group law and inversion on points, containing the unit, killed by $\ell$, stable under $\Lambda$, meeting the level-$N$ structure of $E'$ only in the unit, finite flat and locally of finite presentation over $\operatorname{Spec} k$ of fibre rank $\ell^2$, whose geometric points over any algebraically closed field where $\ell$ is invertible form a group isomorphic to $(\mathbb{Z}/\ell)^2$ — such that the pair $(E',K')$ is an $\ell$-level isogeny onto $E$ in the same sense.
--
--   This is the symmetry of the $\ell$-isogeny correspondence on the Shimura curve attached to $\Lambda$: the dual of an $\ell$-level isogeny $(E,K) \to E'$ is again an $\ell$-level isogeny $(E', \ker\psi) \to E$, so that the two degeneracy maps from the curve with level raised at $\ell$ are exchanged. It is used in the construction of the correspondence itself, by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_withExtraLevel_isLevelIsogeny).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_symm_of_not_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_symm_of_not_dvd
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0) (hNk : (N : k) ≠ 0)
    (hℓN : ¬ ℓ ∣ N)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) (E' : FakeEllipticCurve Λ N k)
    (h : FakeEllipticCurve.IsLevelIsogeny ℓ u E') :
    ∃ K' : E'.ExtraLevel ℓ, FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E', K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) u.1 := by sorry
