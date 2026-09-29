-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fin_forall_factorsThrough_iff_of_iso_of_isLevelIsogeny
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fin_forall_factorsThrough_iff_of_iso_of_isLevelIsogeny
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/669a0725-f149-5544-ae8b-f2b078b29407
-- title:
--   Rigidity of extra level-ℓ structures off finitely many classes
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q\in v$ or $q'\in v$; let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $N\geq 1$, and let $\ell$ be a prime with $\ell\neq q$ and $\ell\neq q'$. Then there are a natural number $n$ and a family $T_0,\dots,T_{n-1}$ of fake elliptic curves with $\Lambda$-multiplication and level-$N$ data over $\overline{\mathbb{Q}}$ with the following property. Let $E$ be such a fake elliptic curve over $\overline{\mathbb{Q}}$ admitting no isomorphism (a scheme isomorphism over the base respecting the relative group law, commuting with the $\Lambda$-action, and matching the level subschemes on points) with any $T_i$. Let $K,K'$ be extra level structures on $E$ at $\ell$, that is closed immersions $K\hookrightarrow E.A$ whose points form a $\Lambda$-stable subgroup of the $\ell$-torsion, disjoint from the level-$N$ subscheme, finite flat of finite presentation of fibre rank $\ell^2$ and with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$. Let $d,d'$ be fake elliptic curves such that $d$ is a level-$\ell$ isogeny quotient of $(E,K)$ and $d'$ one of $(E,K')$, in the sense of `IsLevelIsogeny` (a $\Lambda$-equivariant homomorphism with a quasi-inverse composing to multiplication by $\ell$, whose kernel on points is exactly the given extra level, and which carries the level-$N$ data forward), and suppose $d$ and $d'$ are isomorphic. Then for every scheme $T'$, every morphism $t\colon T'\to\operatorname{Spec}\overline{\mathbb{Q}}$ and every point $P$ of $E$ over $t$, $P$ factors through $K$ if and only if it factors through $K'$.
--
--   A rigidity statement for fake elliptic curves: away from finitely many isomorphism classes, a fake elliptic curve over $\overline{\mathbb{Q}}$ with quaternionic multiplication by a maximal order in an indefinite algebra ramified exactly at $q,q'$ cannot have two distinct extra level-$\ell$ structures with isomorphic quotients, equality of the two structures being expressed as agreement of the subfunctors of points they define. It is used in the construction of the moduli tower entering the Čerednik–Drinfeld comparison, via [`CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_finite_restrictAlong_phi_injOn_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_finite_restrictAlong_phi_injOn_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fin_forall_factorsThrough_iff_of_iso_of_isLevelIsogeny.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fin_forall_factorsThrough_iff_of_iso_of_isLevelIsogeny
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ (n : ℕ) (T : Fin n → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      ∀ (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)), (∀ i : Fin n, ¬ FakeEllipticCurve.Iso E (T i)) →
        ∀ (K K' : E.ExtraLevel ℓ) (d d' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
          FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E, K⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d →
          FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E, K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d' →
          FakeEllipticCurve.Iso d d' →
            ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P := by sorry
